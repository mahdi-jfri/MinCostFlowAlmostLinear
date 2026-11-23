module

public import MinCostFlow.LinkCut.Prog.MathForestExposePhase1

/-!
# Expose Loop Iteration (`splay ;; exposeIterSpliceStmt`) Word-RAM Proof

Proves `exposeIter_runs`: one iteration of the `exposeBody` splice loop preserves
`LctExposeInvs`, strictly increases the exposed path tree size `treeSize`, and satisfies the
Sleator–Tarjan potential + heavy-edge step inequality (including `+ 2` loop-guard overhead).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

theorem exposeIter_runs {w h L P b n v hp0 pos BUDGET : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {t_y : AuxTree} {rest₀ : List AuxTree}
    (p : Program) (sp : SplayProcs) (mem_safe mem₀ : ℕ → ℕ) (r₀ : ℕ → ℕ)
    (hp_has : p.HasAt sp.numZero (splayBodies sp h))
    (hp_base : ∃ spB, sp = SplayProcs.atBase spB)
    (hp_ok : SplayProgramOk w h p sp)
    (hz0_safe : SlotZeroOk mem_safe (lctNodesBase b))
    (harena_safe : lctArenaHi b (lctCap n) ≤ hp0)
    (hsafe₀ : SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 mem₀)
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (t_y :: rest₀) mem₀)
    (hv : v < n)
    (_hz₀ : ZeroFrom mem₀ (mem₀ (lctNodesBase b - 1)))
    (hy_ne : t_y ≠ .leaf)
    (hy_last : (t_y.evalInorder (revFlag mem₀ (lctNodesBase b)) false).getLast? = some (v + 1))
    (hpp_nz : nodeField mem₀ (lctNodesBase b) t_y.rootId OFF_PPAR ≠ 0)
    (hr0_0 : r₀ 0 = lctNodesBase b) (hr0_1 : r₀ 1 = v + 1)
    (hr0_5 : r₀ 5 = t_y.rootId)
    (hr0_6 : r₀ 6 = nodeField mem₀ (lctNodesBase b) t_y.rootId OFF_PPAR)
    (hbudget_w : BUDGET < 2 ^ w)
    (hhp_inv : mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
      (3 * K_SPLAY_STEP L + M_EXPOSE L) *
        (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n))) +
      6000 * (L + 1) * (n + 2) ≤ BUDGET) :
    ∀ ω, ∃ st₂ c₂ t_next rest₂,
      Runs w p ω (Stmt.call 10 sp.splay [.reg 0, .reg 6] ;; exposeIterSpliceStmt sp)
        { mem := mem₀, regs := r₀, pos := pos } .normal st₂ c₂ ∧
      LctExposeInvs w h L P b n freeEdges edgeMap (t_next :: rest₂) st₂.mem ∧
      SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 st₂.mem ∧
      LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1))
        (lctNodesBase b - 1) mem₀ st₂.mem ∧
      (∀ u, lctAuxParent st₂.mem (lctNodesBase b) (lctCap n) u =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap n) u) ∧
      t_next ≠ .leaf ∧
      st₂.regs 0 = lctNodesBase b ∧ st₂.regs 1 = v + 1 ∧ st₂.regs 5 = t_next.rootId ∧
      st₂.regs 6 = nodeField st₂.mem (lctNodesBase b) t_next.rootId OFF_PPAR ∧
      (t_next.evalInorder (revFlag st₂.mem (lctNodesBase b)) false).getLast? = some (v + 1) ∧
      t_y.treeSize (lctVSize mem₀ (lctNodesBase b) (lctCap n)) + 1 ≤
        t_next.treeSize (lctVSize st₂.mem (lctNodesBase b) (lctCap n)) ∧
      c₂ + 2 + (st₂.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st₂.mem b n +
        (3 * K_SPLAY_STEP L + M_EXPOSE L) *
          (Nat.log 2 (n + 2) + 1 - t_next.rank (lctVSize st₂.mem (lctNodesBase b) (lctCap n))) ≤
        lctPhi L mem₀ b n +
          (3 * K_SPLAY_STEP L + M_EXPOSE L) *
            (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n))) := by
  intro ω
  set nb := lctNodesBase b
  set cap := lctCap n
  let y := t_y.rootId
  let pp := nodeField mem₀ nb y OFF_PPAR
  have hnb3 : 3 ≤ nb := hi.sf.2.2.1
  have harena₀ : nb + NODE_STRIDE * (cap + 1) ≤ mem₀ (nb - 1) := hi.sf.2.2.2.1
  have hL₀ : mem₀ (nb - 3) = L := hi.sf.2.2.2.2.1
  have hhp₀ : mem₀ (nb - 1) < 2 ^ w := hi.sf.2.2.2.2.2.1
  have hbase_w : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := lt_of_le_of_lt harena₀ hhp₀
  have hstride_w : NODE_STRIDE < 2 ^ w := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  have hy_tok := hi.sf.trees_ok t_y (by simp)
  have hpp_aux := (hi.auxPathOk t_y (by simp)).2.1
  have hpp_b : 1 ≤ pp ∧ pp ≤ cap ∧ pp ∉ freeEdges := by
    rcases hpp_aux with h0 | hok
    · exact absurd h0 hpp_nz
    · exact hok
  have hpp_notin_y : pp ∉ t_y.toList :=
    lct_cycleFree_ppar_notin hi.sf hi.subdivOk.1 hi.ppar_le_cap (by simp)
  have hpp_flat : pp ∈ (t_y :: rest₀).flatMap AuxTree.toList :=
    hi.sf.perm.symm.mem_iff.1 (List.mem_map.2 ⟨pp - 1, List.mem_range.2 (by omega), by omega⟩)
  rcases List.mem_flatMap.1 hpp_flat with ⟨t_p, htp_mem, hpp_in_p⟩
  have htp_rest : t_p ∈ rest₀ := by
    rcases List.mem_cons.1 htp_mem with rfl | hrest
    · exact absurd hpp_in_p hpp_notin_y
    · exact hrest
  rcases exists_perm_cons_of_mem htp_rest with ⟨rest', hperm_rest⟩
  have hperm_tp : (t_y :: rest₀).Perm (t_p :: t_y :: rest') :=
    (List.Perm.cons t_y hperm_rest).trans (List.Perm.swap t_p t_y rest')
  have htp_free : t_p.rootId ∉ freeEdges := fun hfm => by
    rcases hi.freeNodeOk t_p.rootId hfm with ⟨_, _, htr, _⟩
    have heq := unique_tree_of_mem
      (hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
      htp_mem htr (AuxTree.rootId_mem_toList (hi.sf.trees_ok t_p htp_mem).1)
      (by simp [AuxTree.toList])
    rw [heq, AuxTree.toList] at hpp_in_p
    simp only [List.mem_append, List.mem_singleton] at hpp_in_p
    rcases hpp_in_p with (h | heq_id) | h
    · exact absurd h List.not_mem_nil
    · exact hpp_b.2.2 (heq_id ▸ hfm)
    · exact absurd h List.not_mem_nil
  have hhp_room₀ : mem₀ (nb - 1) + 6000 * (L + 1) * (n + 2) < 2 ^ w := by omega
  have hhp_splay : mem₀ (nb - 1) + K_PUSH_PATH L * (t_p.depthOf pp + 1) + 8 * L * t_p.depthOf pp < 2 ^ w :=
    splay_lct_tree_headroom_lt hi.sf rfl htp_mem hpp_in_p hhp_room₀
  rcases splayForest_lct_runs p sp mem_safe mem₀ nb cap hp0 pos hp_has hp_base hp_ok hz0_safe
      harena_safe hsafe₀ hi.sf hperm_tp hpp_in_p hhp_splay ω with
    ⟨st₁, c₁, t_p', hrun₁, hsf₁, hsafe₁, hr1_id, ht_perm_nodes, hev₁, hsteps₁,
      hrev_p1, hht_p1, hpp_p1, hout₁, hstat₁, hfr₁, hphi₁_all⟩
  have hinv₁ := LctExposeInvs.of_splay hi hperm_tp htp_free hsf₁ hev₁ hsteps₁
    ht_perm_nodes (by simpa [hr1_id] using hpp_p1) hout₁ hstat₁ hfr₁
  rcases hinv₁ with ⟨hi₁, hpar_eq₁, hrep_eq₁, hvs_eq₁, hheavy_eq₁⟩
  cases ht_p' : t_p' with
  | leaf =>
      have hne := (hi₁.sf.trees_ok t_p' (by simp)).1
      exact absurd ht_p' hne
  | node p' l r_old =>
      have hp'_eq : p' = pp := by simpa [ht_p', AuxTree.rootId] using hr1_id
      subst hp'_eq
      rw [ht_p'] at hsf₁ hi₁ hev₁ hsteps₁ ht_perm_nodes
      have hrev_p1_val : nodeField st₁.mem nb pp OFF_REV = 0 := by
        simp only [revFlag, decide_eq_false_iff_not, not_not] at hrev_p1
        exact hrev_p1
      have hcall₁ : Runs w p ω (Stmt.call 10 sp.splay [.reg 0, .reg 6])
          { mem := mem₀, regs := r₀, pos := pos } .normal
          { mem := st₁.mem, regs := Function.update r₀ 10 pp, pos := st₁.pos } (2 + c₁ + 1) := by
        refine runs_call_iff.mpr ⟨[nb, pp], splayBody sp, .returned pp, st₁, c₁, ?_,
          hp_ok.splay_eq, ?_, rfl, ?_, rfl⟩
        · simp [evalArgs, Expr.eval, hr0_0, hr0_6, pp, y]
        · simpa [startState, hr0_0, hr0_6, pp, y] using hrun₁
        · cases st₁; rfl
      let r₁ := Function.update r₀ 10 pp
      have hr₁_0 : r₁ 0 = nb := by simp [r₁, hr0_0]
      have hr₁_1 : r₁ 1 = v + 1 := by simp [r₁, hr0_1]
      have hr₁_5 : r₁ 5 = y := by simp [r₁, hr0_5, y]
      have hr₁_6 : r₁ 6 = pp := by simp [r₁, hr0_6, pp, y]
      have hy_tok₁ := hi₁.sf.trees_ok t_y (by simp)
      have hp_tok₁ := hi₁.sf.trees_ok (.node pp l r_old) (by simp)
      have hy_fields₁ : ∀ u ∈ t_y.toList, ∀ off < NODE_STRIDE,
          nodeField st₁.mem nb u off = nodeField mem₀ nb u off := fun u hu off hoff => by
        have hnin : u ∉ t_p.toList := by
          have hnd := (hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
          have hnd' := (hperm_tp.flatMap (fun _ _ => List.Perm.refl _)).nodup_iff.1 hnd
          rw [List.flatMap_cons, List.nodup_append] at hnd'
          exact fun hm => hnd'.2.2 u hm u (List.mem_flatMap.2 ⟨t_y, by simp, hu⟩) rfl
        exact hout₁ u (hy_tok₁.2.2.nodup_perm_mem (y := u) hu).2 hnin off hoff
      have hy_pp₁ : nodeField st₁.mem nb y OFF_PPAR = pp := by
        rw [hy_fields₁ y (AuxTree.rootId_mem_toList hy_ne) OFF_PPAR (by decide)]
      have hy_last₁ : (t_y.evalInorder (revFlag st₁.mem nb) false).getLast? = some (v + 1) := by
        have hev_y : t_y.evalInorder (revFlag st₁.mem nb) false = t_y.evalInorder (revFlag mem₀ nb) false := by
          apply AuxTree.evalInorder_agree; intro u hu
          simp [revFlag, hy_fields₁ u hu OFF_REV (by decide)]
        rw [hev_y]; exact hy_last
      have hlog_tp : t_p.rank (lctVSize mem₀ nb cap) ≤ Nat.log 2 (n + 2) + 1 :=
        treeRank_le_log_of_invs hi.sf hi.subdivOk.1 hi.auxPathOk htp_mem
      have hvs₁_eq : lctVSize st₁.mem nb cap = lctVSize mem₀ nb cap := funext hvs_eq₁
      have hy_sz_le₁ : t_y.treeSize (lctVSize st₁.mem nb cap) ≤ lctVSize st₁.mem nb cap pp :=
        lctVSize_ge_treeSize_of_ppar hi₁ (by simp) hy_pp₁
      have hy_rk_le_logv : t_y.rank (lctVSize mem₀ nb cap) ≤ Nat.log 2 (1 + lctVSize mem₀ nb cap pp) := by
        rw [← hvs₁_eq]
        have hpos : 1 ≤ t_y.treeSize (lctVSize st₁.mem nb cap) := by
          cases t_y with | leaf => exact absurd rfl hy_ne | node _ _ _ => simp [AuxTree.treeSize]; omega
        unfold AuxTree.rank
        exact Nat.log_mono_right (by omega)
      have hy_rk_le_tp : t_y.rank (lctVSize mem₀ nb cap) ≤ t_p.rank (lctVSize mem₀ nb cap) := by
        have hsub : t_y.treeSize (lctVSize mem₀ nb cap) ≤ lctVSize mem₀ nb cap pp := by
          simpa [← hvs₁_eq] using hy_sz_le₁
        have htp_perm_sz : (AuxTree.node pp l r_old).treeSize (lctVSize st₁.mem nb cap) =
            t_p.treeSize (lctVSize mem₀ nb cap) := by
          rw [hvs₁_eq]
          simpa [ht_p'] using (hphi₁_all (lctVSize mem₀ nb cap)).1
        have hge_tp : lctVSize mem₀ nb cap pp < t_p.treeSize (lctVSize mem₀ nb cap) := by
          rw [← htp_perm_sz, hvs₁_eq]; simp [AuxTree.treeSize]
        unfold AuxTree.rank; exact Nat.log_mono_right (by omega)
      have hphi_splay := (hphi₁_all (lctVSize mem₀ nb cap)).2.2
      have hheavy_count_eq : lctHeavyCount st₁.mem nb cap = lctHeavyCount mem₀ nb cap := hheavy_eq₁
      have hphi₁_step : c₁ + (st₁.mem (nb - 1) - mem₀ (nb - 1)) + lctPhi L st₁.mem b n ≤
          lctPhi L mem₀ b n +
            3 * K_SPLAY_STEP L * (t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap)) +
            C_SPLAY_CONST L := by
        have hdiff_v : 3 * K_SPLAY_STEP L * Nat.log 2 (1 + lctVSize mem₀ nb cap pp) ≥
            3 * K_SPLAY_STEP L * t_y.rank (lctVSize mem₀ nb cap) :=
          Nat.mul_le_mul_left _ hy_rk_le_logv
        have hc_splay : c₁ + (st₁.mem (nb - 1) - mem₀ (nb - 1)) +
            splayMemPhi (K_SPLAY_STEP L) st₁.mem nb cap (lctVSize mem₀ nb cap) +
            3 * K_SPLAY_STEP L * t_y.rank (lctVSize mem₀ nb cap) ≤
            splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap (lctVSize mem₀ nb cap) +
              3 * K_SPLAY_STEP L * t_p.rank (lctVSize mem₀ nb cap) + C_SPLAY_CONST L := by omega
        nth_rw 1 [← hvs₁_eq] at hc_splay
        dsimp only [nb, cap] at *
        rw [Nat.mul_sub_left_distrib]
        unfold lctPhi; rw [hheavy_count_eq] at *; omega
      have hpull_room : st₁.mem (nb - 1) + 4 * L < 2 ^ w := by
        by_cases hhv : isHeavyRoot st₁.mem nb cap y = true
        · have hy_rt_in : y ∈ auxRootIds st₁.mem nb cap :=
            hi₁.sf.auxRootIds_perm.mem_iff.2 (List.mem_map.2 ⟨t_y, by simp, rfl⟩)
          have hhc_pos : 1 ≤ lctHeavyCount st₁.mem nb cap :=
            List.length_pos_of_mem (List.mem_filter.2 ⟨hy_rt_in, hhv⟩)
          have hphi_hv : C_HEAVY L ≤ lctPhi L st₁.mem b n := by
            unfold lctPhi
            have := Nat.mul_le_mul_left (C_HEAVY L) hhc_pos
            dsimp only [nb, cap] at this ⊢; omega
          have hcs_4L : C_SPLAY_CONST L + 4 * L ≤ C_HEAVY L := by unfold C_HEAVY; omega
          have h1 : 3 * K_SPLAY_STEP L * (t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap)) ≤
              (3 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap)) := by
            have hle_diff : t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap) ≤
                Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap) := Nat.sub_le_sub_right hlog_tp _
            exact le_trans (Nat.mul_le_mul_left _ hle_diff) (Nat.mul_le_mul_right _ (by omega))
          have hmem_ge : mem₀ (nb - 1) ≤ st₁.mem (nb - 1) := hfr₁.2.2.1
          omega
        · have hhv_f : isHeavyRoot st₁.mem nb cap y = false := Bool.eq_false_iff.2 hhv
          have hy_lt_half : 2 * dashedChildSize st₁.mem nb cap y ≤ lctRepSize st₁.mem nb cap pp := by
            dsimp only [isHeavyRoot] at hhv_f
            rw [hy_pp₁] at hhv_f
            have hbd : decide (1 ≤ pp ∧ pp ≤ cap) = true := decide_eq_true ⟨hpp_b.1, hpp_b.2.1⟩
            simp only [hbd, Bool.true_and] at hhv_f
            have hne_sq : lctTreeSeq st₁.mem nb cap y ≠ [] := by
              rw [hi₁.sf.lctTreeSeq_eq (by simp)]
              exact auxTree_eval_ne_nil_of_ne_leaf hy_ne
            cases hsq : lctTreeSeq st₁.mem nb cap y with
            | nil => exact absurd hsq hne_sq
            | cons hd tl =>
                simp only [dashedChildSize, hsq] at hhv_f ⊢
                simp only [decide_eq_false_iff_not] at hhv_f; omega
          have hy_sz_eq : dashedChildSize st₁.mem nb cap y = t_y.treeSize (lctVSize st₁.mem nb cap) := by
            have hne_sq : lctTreeSeq st₁.mem nb cap y ≠ [] := by
              rw [hi₁.sf.lctTreeSeq_eq (by simp)]
              exact auxTree_eval_ne_nil_of_ne_leaf hy_ne
            have hts := treeSize_lctVSize_eq_repSize hi₁.sf hi₁.subdivOk.1 hi₁.ppar_le_cap
              (fun s hs => by rw [hi₁.sf.lctTreeSeq_eq hs]; exact auxTree_eval_ne_nil_of_ne_leaf (hi₁.sf.trees_ok s hs).1)
              (t := t_y) (by simp)
            simp only [dashedChildSize]
            cases hsq : lctTreeSeq st₁.mem nb cap y with
            | nil => exact absurd hsq hne_sq
            | cons hd tl => simpa [nb, cap, y, hsq] using hts.symm
          have hpp_le_tp : lctRepSize st₁.mem nb cap pp ≤ t_p.treeSize (lctVSize mem₀ nb cap) := by
            have hne_sq : ∀ s ∈ (AuxTree.node pp l r_old :: t_y :: rest'), lctTreeSeq st₁.mem nb cap s.rootId ≠ [] :=
              fun s hs => by rw [hi₁.sf.lctTreeSeq_eq hs]; exact auxTree_eval_ne_nil_of_ne_leaf (hi₁.sf.trees_ok s hs).1
            have htp_seq := hi₁.sf.lctTreeSeq_eq (t := .node pp l r_old) (by simp)
            rw [AuxTree.rootId] at htp_seq
            have hpp_in_seq : pp ∈ lctTreeSeq st₁.mem nb cap pp := by
              dsimp only [nb, cap]; rw [htp_seq]
              exact ((AuxTree.node pp l r_old).evalInorder_perm _ _).mem_iff.2 (by simp [AuxTree.toList])
            rcases List.getElem_of_mem hpp_in_seq with ⟨idx, hidx, hidx_eq⟩
            have hle_head := lctRepSize_ge_of_tree_idx hi₁.sf hi₁.subdivOk.1 hi₁.ppar_le_cap
              (t := .node pp l r_old) (by simp) idx (by dsimp only [nb, cap, AuxTree.rootId] at hidx ⊢; exact hidx)
            have hsz_head : lctRepSize st₁.mem nb cap ((lctTreeSeq st₁.mem nb cap pp)[0]) =
                (AuxTree.node pp l r_old).treeSize (lctVSize st₁.mem nb cap) := by
              dsimp only [nb, cap]
              have hts_eq := treeSize_lctVSize_eq_repSize hi₁.sf hi₁.subdivOk.1
                hi₁.ppar_le_cap (by dsimp only [nb, cap] at hne_sq; exact hne_sq)
                (t := .node pp l r_old) (by simp)
              cases hts_p : lctTreeSeq st₁.mem (lctNodesBase b) (lctCap n) (AuxTree.node pp l r_old).rootId with
              | nil => exact absurd hts_p (hne_sq (AuxTree.node pp l r_old) (by simp))
              | cons hdp tlp =>
                  simp only [hts_p, List.head_cons] at hts_eq
                  have hts_p' : lctTreeSeq st₁.mem (lctNodesBase b) (lctCap n) pp = hdp :: tlp := by
                    simpa [AuxTree.rootId] using hts_p
                  simp only [hts_p', List.getElem_cons_zero]
                  exact hts_eq.symm
            have htp_perm_sz : (AuxTree.node pp l r_old).treeSize (lctVSize st₁.mem nb cap) =
                t_p.treeSize (lctVSize mem₀ nb cap) := by
              rw [hvs₁_eq]; simpa [ht_p'] using (hphi₁_all (lctVSize mem₀ nb cap)).1
            calc lctRepSize st₁.mem nb cap pp
              _ = lctRepSize st₁.mem nb cap ((lctTreeSeq st₁.mem nb cap pp)[idx]) := by rw [hidx_eq]
              _ ≤ lctRepSize st₁.mem nb cap ((lctTreeSeq st₁.mem nb cap pp)[0]) := by
                  simpa [nb, cap, AuxTree.rootId] using hle_head
              _ = (AuxTree.node pp l r_old).treeSize (lctVSize st₁.mem nb cap) := hsz_head
              _ = t_p.treeSize (lctVSize mem₀ nb cap) := htp_perm_sz
          have hpos_y : 1 ≤ t_y.treeSize (lctVSize mem₀ nb cap) := by
            cases t_y with | leaf => exact absurd rfl hy_ne | node _ _ _ => simp [AuxTree.treeSize]; omega
          have h2y_le_tp : 2 * t_y.treeSize (lctVSize mem₀ nb cap) ≤ t_p.treeSize (lctVSize mem₀ nb cap) := by
            nth_rw 1 [← hvs₁_eq]; rw [← hy_sz_eq]; exact le_trans hy_lt_half hpp_le_tp
          have hrk_strict : t_y.rank (lctVSize mem₀ nb cap) + 1 ≤ t_p.rank (lctVSize mem₀ nb cap) := by
            unfold AuxTree.rank
            refine Nat.le_log_of_pow_le (by omega) ?_
            have hpow : 2 ^ (Nat.log 2 (t_y.treeSize (lctVSize mem₀ nb cap)) + 1) =
                2 * 2 ^ Nat.log 2 (t_y.treeSize (lctVSize mem₀ nb cap)) := by
              rw [Nat.pow_succ, Nat.mul_comm]
            have hpl : 2 ^ Nat.log 2 (t_y.treeSize (lctVSize mem₀ nb cap)) ≤ t_y.treeSize (lctVSize mem₀ nb cap) :=
              Nat.pow_log_le_self 2 (by omega)
            omega
          have hcs_4L : C_SPLAY_CONST L + 4 * L ≤ M_EXPOSE L := by unfold M_EXPOSE C_HEAVY; omega
          have hgap : (3 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap)) ≥
              3 * K_SPLAY_STEP L * (t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap)) + M_EXPOSE L := by
            have hsub_ge : 1 ≤ Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap) := by omega
            have h1 : 3 * K_SPLAY_STEP L * (t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap)) ≤
                3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap)) :=
              Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hlog_tp _)
            have h2 : M_EXPOSE L * 1 ≤ M_EXPOSE L * (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap)) :=
              Nat.mul_le_mul_left _ hsub_ge
            rw [Nat.add_mul]; omega
          have hmem_ge : mem₀ (nb - 1) ≤ st₁.mem (nb - 1) := hfr₁.2.2.1
          dsimp only [nb, cap] at *
          omega
      have harena₁ : nb + NODE_STRIDE * (cap + 1) ≤ st₁.mem (nb - 1) := hi₁.sf.2.2.2.1
      have hL₁ : st₁.mem (nb - 3) = L := hi₁.sf.2.2.2.2.1
      have hhp₁_w : st₁.mem (nb - 1) < 2 ^ w := hi₁.sf.2.2.2.2.2.1
      have hbase₁_w : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := lt_of_le_of_lt harena₁ hhp₁_w
      have hz₁ : ZeroFrom st₁.mem (st₁.mem (nb - 1)) := hi₁.sf.2.2.2.2.2.2.1
      have h0₁ : SlotZeroOk st₁.mem nb := hi₁.sf.2.2.2.2.2.2.2.1
      have hnd_p₁ : (AuxTree.node pp l r_old).toList.Nodup :=
        list_nodup_of_flatMap_nodup
          (hi₁.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
          (by simp)
      have hy_nd₁ : t_y.toList.Nodup :=
        list_nodup_of_flatMap_nodup
          (hi₁.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
          (by simp)
      have hdisj_py : ∀ a ∈ (AuxTree.node pp l r_old).toList, ∀ b ∈ t_y.toList, a ≠ b := by
        intro a ha b hb
        have hnd := hi₁.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
        rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append] at hnd
        exact hnd.2.2 a ha b (List.mem_append.2 (Or.inl hb))
      have hpp_nin_y₁ : pp ∉ t_y.toList := fun hm => hdisj_py pp (by simp [AuxTree.toList]) pp hm rfl
      have hpp_nin_l₁ : pp ∉ l.toList := auxTree_nodup_id_nin_left hnd_p₁
      have hp_ne_y : pp ≠ y := fun h => hpp_nin_y₁ (h ▸ AuxTree.rootId_mem_toList hy_ne)
      have hy_b : 1 ≤ y ∧ y ≤ cap := hy_tok₁.2.2.nodup_perm_mem (y := y) (AuxTree.rootId_mem_toList hy_ne)
      have hptr_p_lt : nb + NODE_STRIDE * pp < 2 ^ w := by
        simpa using nodeAddr_lt_pow hbase₁_w hpp_b.2.1 (by decide : 0 < NODE_STRIDE)
      have hright_p_lt : nb + NODE_STRIDE * pp + OFF_RIGHT < 2 ^ w :=
        nodeAddr_lt_pow hbase₁_w hpp_b.2.1 (by decide : OFF_RIGHT < NODE_STRIDE)
      have hpp_p_lt : nb + NODE_STRIDE * pp + OFF_PPAR < 2 ^ w :=
        nodeAddr_lt_pow hbase₁_w hpp_b.2.1 (by decide : OFF_PPAR < NODE_STRIDE)
      have hptr_y_lt : nb + NODE_STRIDE * y < 2 ^ w := by
        simpa using nodeAddr_lt_pow hbase₁_w hy_b.2 (by decide : 0 < NODE_STRIDE)
      have hpar_y_lt : nb + NODE_STRIDE * y + OFF_PARENT < 2 ^ w :=
        nodeAddr_lt_pow hbase₁_w hy_b.2 (by decide : OFF_PARENT < NODE_STRIDE)
      have hpp_y_lt : nb + NODE_STRIDE * y + OFF_PPAR < 2 ^ w :=
        nodeAddr_lt_pow hbase₁_w hy_b.2 (by decide : OFF_PPAR < NODE_STRIDE)
      have ha7 : Runs w p ω (Stmt.assign 7 (nodePtrExpr 0 6))
          { mem := st₁.mem, regs := r₁, pos := st₁.pos } .normal
          { mem := st₁.mem, regs := Function.update r₁ 7 (nb + NODE_STRIDE * pp), pos := st₁.pos } _ :=
        runs_assign_iff.mpr ⟨nb + NODE_STRIDE * pp,
          eval_nodePtrExpr hstride_w hr₁_0 hr₁_6 hptr_p_lt, rfl, rfl, rfl⟩
      let r₇ := Function.update r₁ 7 (nb + NODE_STRIDE * pp)
      have hr₇_0 : r₇ 0 = nb := by simp [r₇, hr₁_0]
      have hr₇_1 : r₇ 1 = v + 1 := by simp [r₇, hr₁_1]
      have hr₇_5 : r₇ 5 = y := by simp [r₇, hr₁_5]
      have hr₇_6 : r₇ 6 = pp := by simp [r₇, hr₁_6]
      have hr₇_7 : r₇ 7 = nb + NODE_STRIDE * pp := by simp [r₇]
      have ha3 : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 7 OFF_RIGHT))
          { mem := st₁.mem, regs := r₇, pos := st₁.pos } .normal
          { mem := st₁.mem, regs := Function.update r₇ 3 (nodeField st₁.mem nb pp OFF_RIGHT), pos := st₁.pos } _ :=
        runs_assign_iff.mpr ⟨nodeField st₁.mem nb pp OFF_RIGHT,
          eval_fieldLoadExpr hr₇_7 hright_p_lt, rfl, rfl, rfl⟩
      let r₃ := Function.update r₇ 3 (nodeField st₁.mem nb pp OFF_RIGHT)
      have hr₃_0 : r₃ 0 = nb := by simp [r₃, hr₇_0]
      have hr₃_1 : r₃ 1 = v + 1 := by simp [r₃, hr₇_1]
      have hr₃_5 : r₃ 5 = y := by simp [r₃, hr₇_5]
      have hr₃_6 : r₃ 6 = pp := by simp [r₃, hr₇_6]
      have hr₃_7 : r₃ 7 = nb + NODE_STRIDE * pp := by simp [r₃, hr₇_7]
      have hr₃_3 : r₃ 3 = nodeField st₁.mem nb pp OFF_RIGHT := by simp [r₃]
      have hw0₁ : (0 : ℕ) < 2 ^ w := Nat.zero_lt_of_lt hhp₁_w
      have hnb1_ne_slot : ∀ q off, 1 ≤ q → off < NODE_STRIDE → nb - 1 ≠ nb + NODE_STRIDE * q + off := by
        intro q off hq _; unfold NODE_STRIDE; omega
      have hdetach_cond : ∃ mem_d c_d,
          Runs w p ω
            (Stmt.cond (.reg 3)
              (Stmt.assign 4 (nodePtrExpr 0 3) ;;
               Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.const 0) ;;
               Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.reg 6))
              Stmt.nop)
            { mem := st₁.mem, regs := r₃, pos := st₁.pos } .normal
            { mem := mem_d, regs := if r_old = .leaf then r₃ else Function.update r₃ 4 (nb + NODE_STRIDE * r_old.rootId), pos := st₁.pos } c_d ∧
          c_d ≤ 30 ∧ mem_d (nb - 1) = st₁.mem (nb - 1) ∧
          (∀ q off, off < NODE_STRIDE →
            (r_old ≠ .leaf → q = r_old.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
            nodeField mem_d nb q off = nodeField st₁.mem nb q off) ∧
          (r_old ≠ .leaf → nodeField mem_d nb r_old.rootId OFF_PARENT = 0 ∧
            nodeField mem_d nb r_old.rootId OFF_PPAR = pp) ∧
          LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) st₁.mem mem_d ∧
          SafeMem mem_safe nb cap hp0 mem_d := by
        cases hr_c : r_old with
        | leaf =>
            have hro : nodeField st₁.mem nb pp OFF_RIGHT = 0 := by
              dsimp only [nb]; rw [hr_c] at hp_tok₁; exact hp_tok₁.2.2.2.2.2.1
            have hc := (runs_cond_iff (w := w) (p := p) (ω := ω) (e := .reg 3)
                (s := (Stmt.assign 4 (nodePtrExpr 0 3) ;;
                  Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.const 0) ;;
                  Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.reg 6)))
                (t := Stmt.nop) (st := { mem := st₁.mem, regs := r₃, pos := st₁.pos })
                (o := .normal) (st' := { mem := st₁.mem, regs := r₃, pos := st₁.pos })).mpr
              ⟨0, 1, by simp [Expr.eval, hr₃_3, hro], by simp [runs_nop_iff], rfl⟩
            refine ⟨st₁.mem, _, by simpa [hr_c] using hc, ?_, rfl, fun _ _ _ _ => rfl, fun h => absurd rfl h,
              lctFrame_refl (by unfold NODE_STRIDE; omega) harena₁ hz₁, hsafe₁⟩
            simp
        | node rc rl rr =>
            have hrc_eq : nodeField st₁.mem nb pp OFF_RIGHT = rc := by
              dsimp only [nb]; rw [hr_c, AuxTree.rootId] at hp_tok₁; exact hp_tok₁.2.2.2.2.2.1
            have hrc_b : 1 ≤ rc ∧ rc ≤ cap :=
              hp_tok₁.2.2.nodup_perm_mem (y := rc) (by simp [hr_c, AuxTree.toList])
            have hrc_ne0 : rc ≠ 0 := by omega
            have hrc_ptr_lt : nb + NODE_STRIDE * rc < 2 ^ w := by
              simpa using nodeAddr_lt_pow hbase₁_w hrc_b.2 (by decide : 0 < NODE_STRIDE)
            have hrc_par_lt : nb + NODE_STRIDE * rc + OFF_PARENT < 2 ^ w :=
              nodeAddr_lt_pow hbase₁_w hrc_b.2 (by decide : OFF_PARENT < NODE_STRIDE)
            have hrc_pp_lt : nb + NODE_STRIDE * rc + OFF_PPAR < 2 ^ w :=
              nodeAddr_lt_pow hbase₁_w hrc_b.2 (by decide : OFF_PPAR < NODE_STRIDE)
            have ha4 : Runs w p ω (Stmt.assign 4 (nodePtrExpr 0 3))
                { mem := st₁.mem, regs := r₃, pos := st₁.pos } .normal
                { mem := st₁.mem, regs := Function.update r₃ 4 (nb + NODE_STRIDE * rc), pos := st₁.pos } _ :=
              runs_assign_iff.mpr ⟨nb + NODE_STRIDE * rc,
                eval_nodePtrExpr hstride_w hr₃_0 (by dsimp only; rw [hr₃_3, hrc_eq]) hrc_ptr_lt, rfl, rfl, rfl⟩
            let r₄ := Function.update r₃ 4 (nb + NODE_STRIDE * rc)
            have hr₄_4 : r₄ 4 = nb + NODE_STRIDE * rc := by simp [r₄]
            have hr₄_6 : r₄ 6 = pp := by simp [r₄, hr₃_6]
            have hs1 : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.const 0))
                { mem := st₁.mem, regs := r₄, pos := st₁.pos } .normal
                { mem := Function.update st₁.mem (nb + NODE_STRIDE * rc + OFF_PARENT) 0, regs := r₄, pos := st₁.pos } _ :=
              runs_store_iff.mpr ⟨nb + NODE_STRIDE * rc + OFF_PARENT, 0,
                eval_fieldAddrExpr hr₄_4 hrc_par_lt, Expr.eval_const hw0₁, rfl, rfl, rfl⟩
            let md₁ := Function.update st₁.mem (nb + NODE_STRIDE * rc + OFF_PARENT) 0
            have hs2 : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.reg 6))
                { mem := md₁, regs := r₄, pos := st₁.pos } .normal
                { mem := Function.update md₁ (nb + NODE_STRIDE * rc + OFF_PPAR) pp, regs := r₄, pos := st₁.pos } _ :=
              runs_store_iff.mpr ⟨nb + NODE_STRIDE * rc + OFF_PPAR, pp,
                eval_fieldAddrExpr hr₄_4 hrc_pp_lt, Expr.eval_reg_of_eq hr₄_6, rfl, rfl, rfl⟩
            let md₂ := Function.update md₁ (nb + NODE_STRIDE * rc + OFF_PPAR) pp
            have hcond_then := runs_seq_normal ha4 (runs_seq_normal hs1 hs2)
            have hcond := (runs_cond_iff (e := .reg 3)
                (st := { mem := st₁.mem, regs := r₃, pos := st₁.pos }) (t := Stmt.nop)).mpr
              ⟨rc, _, by simp [Expr.eval, hr₃_3, hrc_eq], by simpa [hrc_ne0] using hcond_then, rfl⟩
            have hfr_d : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) st₁.mem md₂ := by
              have hmul1 : NODE_STRIDE ≤ NODE_STRIDE * rc := Nat.le_mul_of_pos_right _ hrc_b.1
              have hb1 := slot_lt_of_arena hrc_b.2 (by decide : OFF_PARENT < NODE_STRIDE)
                (le_refl (nb + NODE_STRIDE * (cap + 1)))
              have hb2 := slot_lt_of_arena hrc_b.2 (by decide : OFF_PPAR < NODE_STRIDE)
                (le_refl (nb + NODE_STRIDE * (cap + 1)))
              have hhdr : nb - 1 < nb + NODE_STRIDE := by unfold NODE_STRIDE; omega
              have f1 : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) st₁.mem md₁ :=
                lctFrame_update_arena (val := 0) (by omega) hb1 hhdr harena₁ hz₁
              have f2 : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) md₁ md₂ :=
                lctFrame_update_arena (val := pp) (mem := md₁) (by omega) hb2 hhdr
                  (le_trans f1.2.1 f1.2.2.1) f1.2.2.2.2.1
              exact lctFrame_trans f1 f2
            have hhp_d : md₂ (nb - 1) = st₁.mem (nb - 1) := by
              dsimp only [md₂, md₁]
              rw [Function.update_of_ne (hnb1_ne_slot rc OFF_PPAR hrc_b.1 (by decide)),
                Function.update_of_ne (hnb1_ne_slot rc OFF_PARENT hrc_b.1 (by decide))]
            have hsafe_d : SafeMem mem_safe nb cap hp0 md₂ :=
              SafeMem.update_struct hrc_b.1 hrc_b.2 hpp_b.2.1 (Or.inr (Or.inr (Or.inr rfl)))
                (SafeMem.update_struct hrc_b.1 hrc_b.2 (Nat.zero_le _) (Or.inr (Or.inr (Or.inl rfl))) hsafe₁)
            refine ⟨md₂, _, by simpa [hr_c, AuxTree.rootId] using hcond, ?_, hhp_d, ?_, ?_, hfr_d, hsafe_d⟩
            · simp [Expr.size, nodePtrExpr, fieldAddrExpr]
            · intro q off hoff hne
              dsimp only [nodeField, md₂, md₁]
              have e1 : nb + NODE_STRIDE * q + off ≠ nb + NODE_STRIDE * rc + OFF_PPAR := fun h => by
                have := slot_addr_inj hoff (by decide) h
                exact (hne (by simp) this.1).2 this.2
              have e2 : nb + NODE_STRIDE * q + off ≠ nb + NODE_STRIDE * rc + OFF_PARENT := fun h => by
                have := slot_addr_inj hoff (by decide) h
                exact (hne (by simp) this.1).1 this.2
              rw [Function.update_of_ne e1, Function.update_of_ne e2]
            · intro _
              simp only [AuxTree.rootId, nodeField, md₂, md₁]
              exact ⟨by rw [Function.update_of_ne (by unfold OFF_PARENT OFF_PPAR; omega), Function.update_self],
                Function.update_self _ _ _⟩
      rcases hdetach_cond with ⟨mem_d, c_d, hrun_d, hc_d, hhp_d, hd_fields, hd_rc, hfr_d, hsafe_d⟩
      let r_d := if r_old = .leaf then r₃ else Function.update r₃ 4 (nb + NODE_STRIDE * r_old.rootId)
      have hrd_0 : r_d 0 = nb := by dsimp only [r_d]; split_ifs <;> simp [hr₃_0]
      have hrd_1 : r_d 1 = v + 1 := by dsimp only [r_d]; split_ifs <;> simp [hr₃_1]
      have hrd_5 : r_d 5 = y := by dsimp only [r_d]; split_ifs <;> simp [hr₃_5]
      have hrd_6 : r_d 6 = pp := by dsimp only [r_d]; split_ifs <;> simp [hr₃_6]
      have hrd_7 : r_d 7 = nb + NODE_STRIDE * pp := by dsimp only [r_d]; split_ifs <;> simp [hr₃_7]
      have hs_r : Runs w p ω (Stmt.store (fieldAddrExpr 7 OFF_RIGHT) (.reg 5))
          { mem := mem_d, regs := r_d, pos := st₁.pos } .normal
          { mem := Function.update mem_d (nb + NODE_STRIDE * pp + OFF_RIGHT) y, regs := r_d, pos := st₁.pos } _ :=
        runs_store_iff.mpr ⟨nb + NODE_STRIDE * pp + OFF_RIGHT, y,
          eval_fieldAddrExpr hrd_7 hright_p_lt, Expr.eval_reg_of_eq hrd_5, rfl, rfl, rfl⟩
      let m_s1 := Function.update mem_d (nb + NODE_STRIDE * pp + OFF_RIGHT) y
      have ha8 : Runs w p ω (Stmt.assign 8 (nodePtrExpr 0 5))
          { mem := m_s1, regs := r_d, pos := st₁.pos } .normal
          { mem := m_s1, regs := Function.update r_d 8 (nb + NODE_STRIDE * y), pos := st₁.pos } _ :=
        runs_assign_iff.mpr ⟨nb + NODE_STRIDE * y,
          eval_nodePtrExpr hstride_w hrd_0 hrd_5 hptr_y_lt, rfl, rfl, rfl⟩
      let r₈ := Function.update r_d 8 (nb + NODE_STRIDE * y)
      have hr₈_0 : r₈ 0 = nb := by simp [r₈, hrd_0]
      have hr₈_1 : r₈ 1 = v + 1 := by simp [r₈, hrd_1]
      have hr₈_6 : r₈ 6 = pp := by simp [r₈, hrd_6]
      have hr₈_7 : r₈ 7 = nb + NODE_STRIDE * pp := by simp [r₈, hrd_7]
      have hr₈_8 : r₈ 8 = nb + NODE_STRIDE * y := by simp [r₈]
      have hs_yp : Runs w p ω (Stmt.store (fieldAddrExpr 8 OFF_PARENT) (.reg 6))
          { mem := m_s1, regs := r₈, pos := st₁.pos } .normal
          { mem := Function.update m_s1 (nb + NODE_STRIDE * y + OFF_PARENT) pp, regs := r₈, pos := st₁.pos } _ :=
        runs_store_iff.mpr ⟨nb + NODE_STRIDE * y + OFF_PARENT, pp,
          eval_fieldAddrExpr hr₈_8 hpar_y_lt, Expr.eval_reg_of_eq hr₈_6, rfl, rfl, rfl⟩
      let m_s2 := Function.update m_s1 (nb + NODE_STRIDE * y + OFF_PARENT) pp
      have hs_ypp : Runs w p ω (Stmt.store (fieldAddrExpr 8 OFF_PPAR) (.const 0))
          { mem := m_s2, regs := r₈, pos := st₁.pos } .normal
          { mem := Function.update m_s2 (nb + NODE_STRIDE * y + OFF_PPAR) 0, regs := r₈, pos := st₁.pos } _ :=
        runs_store_iff.mpr ⟨nb + NODE_STRIDE * y + OFF_PPAR, 0,
          eval_fieldAddrExpr hr₈_8 hpp_y_lt, Expr.eval_const hw0₁, rfl, rfl, rfl⟩
      let mem_ptr := Function.update m_s2 (nb + NODE_STRIDE * y + OFF_PPAR) 0
      have hfr_d_ptr : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem_d mem_ptr :=
        lctFrame_three_slot_updates hpp_b.1 hpp_b.2.1 (by decide) hy_b.1 hy_b.2 (by decide)
          hy_b.1 hy_b.2 (by decide) (by rw [hhp_d]; exact harena₁) (by simpa [hhp_d] using hfr_d.2.2.2.2.1) hnb3
      have hfr_1_ptr := lctFrame_trans hfr_d hfr_d_ptr
      have hhp_ptr : mem_ptr (nb - 1) = st₁.mem (nb - 1) := by
        dsimp only [mem_ptr, m_s2, m_s1]
        rw [Function.update_of_ne (hnb1_ne_slot y OFF_PPAR hy_b.1 (by decide)),
          Function.update_of_ne (hnb1_ne_slot y OFF_PARENT hy_b.1 (by decide)),
          Function.update_of_ne (hnb1_ne_slot pp OFF_RIGHT hpp_b.1 (by decide)), hhp_d]
      have hz_ptr : ZeroFrom mem_ptr (mem_ptr (nb - 1)) := hfr_1_ptr.2.2.2.2.1
      have hsafe_ptr : SafeMem mem_safe nb cap hp0 mem_ptr :=
        SafeMem.update_struct hy_b.1 hy_b.2 (Nat.zero_le _) (Or.inr (Or.inr (Or.inr rfl)))
          (SafeMem.update_struct hy_b.1 hy_b.2 hpp_b.2.1 (Or.inr (Or.inr (Or.inl rfl)))
            (SafeMem.update_struct hpp_b.1 hpp_b.2.1 hy_b.2 (Or.inr (Or.inl rfl)) hsafe_d))
      have h0_ptr : SlotZeroOk mem_ptr nb := fun off hoff => by
        dsimp only [mem_ptr, m_s2, m_s1]
        have h1 : nb + off ≠ nb + NODE_STRIDE * y + OFF_PPAR := fun h => by
          have := (slot_addr_inj (y₁ := 0) (o₁ := off) (o₂ := OFF_PPAR) hoff (by decide) (by simpa using h)).1
          omega
        have h2 : nb + off ≠ nb + NODE_STRIDE * y + OFF_PARENT := fun h => by
          have := (slot_addr_inj (y₁ := 0) (o₁ := off) (o₂ := OFF_PARENT) hoff (by decide) (by simpa using h)).1
          omega
        have h3 : nb + off ≠ nb + NODE_STRIDE * pp + OFF_RIGHT := fun h => by
          have := (slot_addr_inj (y₁ := 0) (o₁ := off) (o₂ := OFF_RIGHT) hoff (by decide) (by simpa using h)).1
          omega
        rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
        have heq := hd_fields 0 off hoff (fun hne he0 => by
          have : r_old.rootId ≠ 0 := by cases r_old with | leaf => exact absurd rfl hne | node rc _ _ =>
            have := hp_tok₁.2.2.nodup_perm_mem (y := rc) (by simp [AuxTree.toList])
            simp only [AuxTree.rootId]; omega
          exact absurd he0.symm this)
        exact heq.trans (h0₁ off hoff)
      have hL_ptr : mem_ptr (nb - 3) = L := by
        dsimp only [mem_ptr, m_s2, m_s1]
        rw [Function.update_of_ne (by unfold NODE_STRIDE; omega),
          Function.update_of_ne (by unfold NODE_STRIDE; omega),
          Function.update_of_ne (by unfold NODE_STRIDE; omega),
          hfr_d.2.2.2.2.2 (nb - 3) (Or.inl ⟨by unfold NODE_STRIDE; omega, by omega⟩), hL₁]
      have hptr_field : ∀ q off, off < NODE_STRIDE →
          (¬(q = pp ∧ off = OFF_RIGHT) ∧ ¬(q = y ∧ off = OFF_PARENT) ∧ ¬(q = y ∧ off = OFF_PPAR)) →
          (r_old ≠ .leaf → q = r_old.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField mem_ptr nb q off = nodeField st₁.mem nb q off := by
        intro q off hoff ⟨hn1, hn2, hn3⟩ hne_r
        dsimp only [nodeField, mem_ptr, m_s2, m_s1]
        have e1 : nb + NODE_STRIDE * q + off ≠ nb + NODE_STRIDE * y + OFF_PPAR := fun h =>
          hn3 (slot_addr_inj hoff (by decide) h)
        have e2 : nb + NODE_STRIDE * q + off ≠ nb + NODE_STRIDE * y + OFF_PARENT := fun h =>
          hn2 (slot_addr_inj hoff (by decide) h)
        have e3 : nb + NODE_STRIDE * q + off ≠ nb + NODE_STRIDE * pp + OFF_RIGHT := fun h =>
          hn1 (slot_addr_inj hoff (by decide) h)
        rw [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_of_ne e3]
        exact hd_fields q off hoff hne_r
      have hr_nin_y : ∀ u ∈ t_y.toList, r_old ≠ .leaf → u ≠ r_old.rootId := fun u hu hne heq =>
        hdisj_py u (by rw [heq]; simp [AuxTree.toList, AuxTree.rootId_mem_toList hne]) u hu rfl
      have hr_nin_l : ∀ u ∈ l.toList, r_old ≠ .leaf → u ≠ r_old.rootId := fun u hu hne heq => by
        have hnd' := hnd_p₁; rw [AuxTree.toList, List.nodup_append] at hnd'
        exact hnd'.2.2 u (by simp [hu]) u (by rw [heq]; simp [AuxTree.rootId_mem_toList hne]) rfl
      have hp_ne_rold : r_old ≠ .leaf → pp ≠ r_old.rootId := fun hne heq => by
        have hnd' := hnd_p₁; rw [AuxTree.toList, List.nodup_append] at hnd'
        exact hnd'.2.2 pp (by simp) pp (by rw [heq]; simp [AuxTree.rootId_mem_toList hne]) rfl
      have hp_left_eq : nodeField mem_ptr nb pp OFF_LEFT = l.rootId := by
        rw [hptr_field pp OFF_LEFT (by decide) ⟨fun h => absurd h.2 (by decide), fun h => hp_ne_y h.1, fun h => hp_ne_y h.1⟩
          (fun h1 h2 => absurd h2 (hp_ne_rold h1))]
        exact hp_tok₁.2.2.2.2.1
      have hp_right_eq : nodeField mem_ptr nb pp OFF_RIGHT = y := by
        dsimp only [nodeField, mem_ptr, m_s2, m_s1]
        have e1 : nb + NODE_STRIDE * pp + OFF_RIGHT ≠ nb + NODE_STRIDE * y + OFF_PPAR := fun h =>
          hp_ne_y (slot_addr_inj (by decide) (by decide) h).1
        have e2 : nb + NODE_STRIDE * pp + OFF_RIGHT ≠ nb + NODE_STRIDE * y + OFF_PARENT := fun h =>
          hp_ne_y (slot_addr_inj (by decide) (by decide) h).1
        rw [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_self]
      have hp_par_eq : nodeField mem_ptr nb pp OFF_PARENT = 0 := by
        rw [hptr_field pp OFF_PARENT (by decide) ⟨fun h => absurd h.2 (by decide), fun h => hp_ne_y h.1, fun h => hp_ne_y h.1⟩
          (fun h1 h2 => absurd h2 (hp_ne_rold h1))]
        exact hp_tok₁.2.2.2.2.2.2.1
      have hp_pp_eq : nodeField mem_ptr nb pp OFF_PPAR = nodeField st₁.mem nb pp OFF_PPAR :=
        hptr_field pp OFF_PPAR (by decide) ⟨fun h => absurd h.2 (by decide), fun h => hp_ne_y h.1, fun h => hp_ne_y h.1⟩
          (fun h1 h2 => absurd h2 (hp_ne_rold h1))
      have hy_par_ptr : nodeField mem_ptr nb y OFF_PARENT = pp := by
        dsimp only [nodeField, mem_ptr, m_s2]
        rw [Function.update_of_ne (by unfold OFF_PARENT OFF_PPAR; omega), Function.update_self]
      have hy_pp_ptr : nodeField mem_ptr nb y OFF_PPAR = 0 := by
        dsimp only [nodeField, mem_ptr]; exact Function.update_self _ _ _
      have hl_fields_ptr : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          nodeField mem_ptr nb u off = nodeField st₁.mem nb u off := fun u hu off hoff =>
        hptr_field u off hoff
          ⟨fun h => hpp_nin_l₁ (h.1 ▸ hu), fun h => hdisj_py u (by simp [AuxTree.toList, hu]) y
            (AuxTree.rootId_mem_toList hy_ne) h.1, fun h => hdisj_py u (by simp [AuxTree.toList, hu]) y
            (AuxTree.rootId_mem_toList hy_ne) h.1⟩
          (fun h1 h2 => absurd h2 (hr_nin_l u hu h1))
      have hy_fields_ptr : ∀ u ∈ t_y.toList, ∀ off < NODE_STRIDE,
          (u = y → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField mem_ptr nb u off = nodeField st₁.mem nb u off := fun u hu off hoff hne =>
        hptr_field u off hoff
          ⟨fun h => hpp_nin_y₁ (h.1 ▸ hu), fun h => (hne h.1).1 h.2, fun h => (hne h.1).2 h.2⟩
          (fun h1 h2 => absurd h2 (hr_nin_y u hu h1))
      have hheap_ptr : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < st₁.mem (nb - 1) → mem_ptr a = st₁.mem a :=
        fun a ha ha' => hfr_1_ptr.2.2.2.2.2 a (Or.inr ⟨ha, ha'⟩)
      have hp_tok_tm : TreeMemMatch w h L st₁.mem nb cap (.node pp l r_old) 0
          (nodeField st₁.mem nb pp OFF_PPAR) := by
        dsimp only [nb, cap]; simpa [AuxTree.rootId] using hp_tok₁.2.2
      have hy_tok_tm : TreeMemMatch w h L st₁.mem nb cap t_y 0 pp := by
        dsimp only [nb, cap, y] at *; simpa [hy_pp₁] using hy_tok₁.2.2
      have hpre_p := pullPre_splice hbase₁_w hp_tok_tm hnd_p₁ hy_tok_tm hy_nd₁ hdisj_py
        hrev_p1_val hht_p1 hhp_ptr hp_left_eq hp_right_eq hp_par_eq hp_pp_eq hy_par_ptr hy_pp_ptr
        (fun off hoff hne => hptr_field pp off hoff ⟨fun h => hne h.2, fun h => hp_ne_y h.1, fun h => hp_ne_y h.1⟩
          (fun h1 h2 => absurd h2 (hp_ne_rold h1)))
        hl_fields_ptr hy_fields_ptr hheap_ptr
      have hrp := pull_lct_runs (pos := st₁.pos) p sp mem_safe mem_ptr hp_has hp_base hp_ok hbase₁_w hnb3 hL_ptr
        harena_safe hz0_safe hsafe_ptr (by rw [hhp_ptr]; exact harena₁) hz_ptr
        (by rw [hhp_ptr]; exact hpull_room) h0_ptr hpp_b.2.1 hpp_nin_l₁ hpp_nin_y₁ hpre_p ω
      rcases hrp with ⟨st₂, c_p, hrun_p, hsafe₂, hc_p, hle_p, hhi_p, htm₂, hout₂, hnonAgg₂, hfr_p⟩
      have hcall_p : Runs w p ω (Stmt.call 10 sp.pull [.reg 0, .reg 6])
          { mem := mem_ptr, regs := r₈, pos := st₁.pos } .normal
          { mem := st₂.mem, regs := Function.update r₈ 10 0, pos := st₂.pos } (2 + c_p + 1) := by
        refine runs_call_iff.mpr ⟨[nb, pp], pullBody sp, .returned 0, st₂, c_p, ?_, hp_ok.pull_eq, ?_, rfl, ?_, rfl⟩
        · simp [evalArgs, Expr.eval, hr₈_0, hr₈_6]
        · simpa [startState, hr₈_0, hr₈_6] using hrun_p
        · cases st₂; rfl
      let r₉ := Function.update r₈ 10 0
      have hr₉_6 : r₉ 6 = pp := by simp [r₉, hr₈_6]
      have hr₉_7 : r₉ 7 = nb + NODE_STRIDE * pp := by simp [r₉, hr₈_7]
      have ha5 : Runs w p ω (Stmt.assign 5 (.reg 6))
          { mem := st₂.mem, regs := r₉, pos := st₂.pos } .normal
          { mem := st₂.mem, regs := Function.update r₉ 5 pp, pos := st₂.pos } _ :=
        runs_assign_iff.mpr ⟨pp, by simp [Expr.eval, hr₉_6], rfl, rfl, rfl⟩
      let r₅ := Function.update r₉ 5 pp
      have hr₅_7 : r₅ 7 = nb + NODE_STRIDE * pp := by simp [r₅, hr₉_7]
      have ha6 : Runs w p ω (Stmt.assign 6 (fieldLoadExpr 7 OFF_PPAR))
          { mem := st₂.mem, regs := r₅, pos := st₂.pos } .normal
          { mem := st₂.mem, regs := Function.update r₅ 6 (nodeField st₂.mem nb pp OFF_PPAR), pos := st₂.pos } _ :=
        runs_assign_iff.mpr ⟨nodeField st₂.mem nb pp OFF_PPAR,
          eval_fieldLoadExpr hr₅_7 hpp_p_lt, rfl, rfl, rfl⟩
      have hsplice_run : Runs w p ω (exposeIterSpliceStmt sp)
          { mem := st₁.mem, regs := r₁, pos := st₁.pos } .normal
          { mem := st₂.mem, regs := Function.update r₅ 6 (nodeField st₂.mem nb pp OFF_PPAR), pos := st₂.pos } _ :=
        runs_seq_normal ha7 (runs_seq_normal ha3 (runs_seq_normal hrun_d
          (runs_seq_normal hs_r (runs_seq_normal ha8 (runs_seq_normal hs_yp
            (runs_seq_normal hs_ypp (runs_seq_normal hcall_p (runs_seq_normal ha5 ha6))))))))
      have hfull_run := runs_seq_normal hcall₁ hsplice_run
      have hfr_1_2 := lctFrame_trans hfr_1_ptr hfr_p
      have hfr_0_2 := lctFrame_trans hfr₁ hfr_1_2
      have hpp_2 : nodeField st₂.mem nb pp OFF_PPAR = nodeField st₁.mem nb pp OFF_PPAR := by
        rw [hnonAgg₂ OFF_PPAR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hp_pp_eq]
      have hout₂_field : ∀ u ≤ cap, ∀ off < NODE_STRIDE, u ≠ pp →
          nodeField st₂.mem nb u off = nodeField mem_ptr nb u off := by
        intro u hu off hoff hup
        have haddr_ok := hout₂ (nb + NODE_STRIDE * u + off)
          (by unfold NODE_STRIDE; omega)
          (slot_disjoint_of_ne hup hoff)
          (by rw [hhp_ptr]; exact slot_lt_of_arena hu hoff harena₁)
        exact haddr_ok
      have hnonAgg_p₂ : ∀ off < NODE_STRIDE, off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
          off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
          off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
          off ≠ OFF_RIGHT → nodeField st₂.mem nb pp off = nodeField st₁.mem nb pp off := by
        intro off hoff h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
        rw [hnonAgg₂ off hoff h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
        exact hptr_field pp off hoff ⟨fun h => h12 h.2, fun h => hp_ne_y h.1, fun h => hp_ne_y h.1⟩
          (fun h1' h2' => absurd h2' (hp_ne_rold h1'))
      have hl_fields₂ : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          nodeField st₂.mem nb u off = nodeField st₁.mem nb u off := fun u hu off hoff => by
        have hup : u ≠ pp := fun h => hpp_nin_l₁ (h ▸ hu)
        rw [hout₂_field u (hp_tok₁.2.2.nodup_perm_mem (y := u) (by simp [AuxTree.toList, hu])).2 off hoff hup]
        exact hl_fields_ptr u hu off hoff
      have hy_fields₂ : ∀ u ∈ t_y.toList, ∀ off < NODE_STRIDE,
          (u = y → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField st₂.mem nb u off = nodeField st₁.mem nb u off := fun u hu off hoff hne => by
        have hup : u ≠ pp := fun h => hpp_nin_y₁ (h ▸ hu)
        rw [hout₂_field u (hy_tok₁.2.2.nodup_perm_mem (y := u) hu).2 off hoff hup]
        exact hy_fields_ptr u hu off hoff hne
      have hl_out₂ : ∀ u ≤ cap, u ∉ (AuxTree.node pp l t_y).toList → ∀ off < NODE_STRIDE,
          (r_old ≠ .leaf → u = r_old.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField st₂.mem nb u off = nodeField st₁.mem nb u off := fun u hu hnin off hoff hnr => by
        have hup : u ≠ pp := fun h => hnin (by simp [AuxTree.toList, h])
        have huy : u ≠ y := fun h => hnin (by
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
          exact Or.inr (h ▸ AuxTree.rootId_mem_toList hy_ne))
        rw [hout₂_field u hu off hoff hup]
        exact hptr_field u off hoff ⟨fun h => hup h.1, fun h => huy h.1, fun h => huy h.1⟩ hnr
      have hr_par₂ : r_old ≠ .leaf → nodeField st₂.mem nb r_old.rootId OFF_PARENT = 0 := fun hr => by
        have hup : r_old.rootId ≠ pp := (hp_ne_rold hr).symm
        have hb := hp_tok₁.2.2.nodup_perm_mem (y := r_old.rootId)
          (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
        rw [hout₂_field r_old.rootId hb.2 OFF_PARENT (by decide) hup]
        dsimp only [nodeField, mem_ptr, m_s2, m_s1]
        have huy : r_old.rootId ≠ y := fun h => hr_nin_y y (AuxTree.rootId_mem_toList hy_ne) hr h.symm
        have e1 : nb + NODE_STRIDE * r_old.rootId + OFF_PARENT ≠ nb + NODE_STRIDE * y + OFF_PPAR :=
          fun h => huy (slot_addr_inj (by decide) (by decide) h).1
        have e2 : nb + NODE_STRIDE * r_old.rootId + OFF_PARENT ≠ nb + NODE_STRIDE * y + OFF_PARENT :=
          fun h => huy (slot_addr_inj (by decide) (by decide) h).1
        have e3 : nb + NODE_STRIDE * r_old.rootId + OFF_PARENT ≠ nb + NODE_STRIDE * pp + OFF_RIGHT :=
          fun h => hup (slot_addr_inj (by decide) (by decide) h).1
        rw [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_of_ne e3]
        exact (hd_rc hr).1
      have hr_pp₂ : r_old ≠ .leaf → nodeField st₂.mem nb r_old.rootId OFF_PPAR = pp := fun hr => by
        have hup : r_old.rootId ≠ pp := (hp_ne_rold hr).symm
        have hb := hp_tok₁.2.2.nodup_perm_mem (y := r_old.rootId)
          (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
        rw [hout₂_field r_old.rootId hb.2 OFF_PPAR (by decide) hup]
        dsimp only [nodeField, mem_ptr, m_s2, m_s1]
        have huy : r_old.rootId ≠ y := fun h => hr_nin_y y (AuxTree.rootId_mem_toList hy_ne) hr h.symm
        have e1 : nb + NODE_STRIDE * r_old.rootId + OFF_PPAR ≠ nb + NODE_STRIDE * y + OFF_PPAR :=
          fun h => huy (slot_addr_inj (by decide) (by decide) h).1
        have e2 : nb + NODE_STRIDE * r_old.rootId + OFF_PPAR ≠ nb + NODE_STRIDE * y + OFF_PARENT :=
          fun h => huy (slot_addr_inj (by decide) (by decide) h).1
        have e3 : nb + NODE_STRIDE * r_old.rootId + OFF_PPAR ≠ nb + NODE_STRIDE * pp + OFF_RIGHT :=
          fun h => hup (slot_addr_inj (by decide) (by decide) h).1
        rw [Function.update_of_ne e1, Function.update_of_ne e2, Function.update_of_ne e3]
        exact (hd_rc hr).2
      have hhp₂ : st₂.mem (nb - 1) < 2 ^ w := by
        rw [hhp_ptr] at hhi_p; dsimp only [nb] at *; omega
      have hsp := LctExposeInvs.of_splice hi₁ hrev_p1_val hht_p1 hy_pp₁ hy_last₁ hv
        (by simpa [nb] using hhp₂) (by simpa [nb] using hpp_2) (by simpa [nb, hpp_2] using htm₂)
        (by simpa [nb] using hl_fields₂) (by simpa [nb] using hy_fields₂)
        (by simpa [nb] using hnonAgg_p₂) (by simpa [nb, cap] using hl_out₂)
        (by simpa [nb] using hr_par₂) (by simpa [nb] using hr_pp₂) hfr_1_2
      rcases hsp with ⟨hi₂, hpar_eq₂, _, hy_le, htop_sz, htop_rk, hphi_eq₂, hhv_t, hlt_f⟩
      let t_next := AuxTree.node pp l t_y
      let rest₂ := if r_old = .leaf then rest' else r_old :: rest'
      have htrees₂_eq : (if r_old = .leaf then AuxTree.node pp l t_y :: rest'
          else AuxTree.node pp l t_y :: r_old :: rest') = t_next :: rest₂ := by
        cases r_old <;> simp [t_next, rest₂]
      have hhi₂' : LctExposeInvs w h L P b n freeEdges edgeMap (t_next :: rest₂) st₂.mem := by
        rw [htrees₂_eq] at hi₂; exact hi₂
      have hpar_all : ∀ u, lctAuxParent st₂.mem nb cap u = lctAuxParent mem₀ nb cap u := fun u =>
        (hpar_eq₂ u).trans (hpar_eq₁ u)
      have hlast_next : (t_next.evalInorder (revFlag st₂.mem nb) false).getLast? = some (v + 1) := by
        have hrv_p2 : nodeField st₂.mem nb pp OFF_REV = 0 := by
          rw [hnonAgg_p₂ OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrev_p1_val]
        have hrev_p2 : revFlag st₂.mem nb pp = false := by simp [revFlag, hrv_p2]
        have hy_eval₂ : t_y.evalInorder (revFlag st₂.mem nb) false = t_y.evalInorder (revFlag st₁.mem nb) false := by
          apply AuxTree.evalInorder_agree; intro u hu
          simp [revFlag, hy_fields₂ u hu OFF_REV (by decide) (fun _ => ⟨by decide, by decide⟩)]
        have hy_ne₂ : t_y.evalInorder (revFlag st₂.mem nb) false ≠ [] := by
          rw [hy_eval₂]; exact auxTree_eval_ne_nil_of_ne_leaf hy_ne
        have h_ev : t_next.evalInorder (revFlag st₂.mem nb) false =
            (l.evalInorder (revFlag st₂.mem nb) false ++ [pp]) ++ t_y.evalInorder (revFlag st₂.mem nb) false := by
          simp [t_next, AuxTree.evalInorder, hrev_p2]
        rw [h_ev, List.getLast?_append_of_ne_nil _ hy_ne₂, hy_eval₂, hy_last₁]
      have hsz_grow : t_y.treeSize (lctVSize mem₀ nb cap) + 1 ≤ t_next.treeSize (lctVSize st₂.mem nb cap) := by
        have htop' : t_next.treeSize (lctVSize st₂.mem nb cap) =
            (AuxTree.node pp l r_old).treeSize (lctVSize st₁.mem nb cap) := htop_sz
        have hge : t_y.treeSize (lctVSize st₁.mem nb cap) + 1 ≤
            (AuxTree.node pp l r_old).treeSize (lctVSize st₁.mem nb cap) := by
          simp only [AuxTree.treeSize]
          omega
        rw [htop']; simpa [← hvs₁_eq] using hge
      have hlog_next : t_next.rank (lctVSize st₂.mem nb cap) ≤ Nat.log 2 (n + 2) + 1 :=
        treeRank_le_log_of_invs hhi₂'.sf hhi₂'.subdivOk.1 hhi₂'.auxPathOk (by simp)
      have htop_rk_tp : t_next.rank (lctVSize st₂.mem nb cap) = t_p.rank (lctVSize mem₀ nb cap) := by
        have hperm_sz : (AuxTree.node pp l r_old).treeSize (lctVSize st₁.mem nb cap) =
            t_p.treeSize (lctVSize mem₀ nb cap) := by
          rw [hvs₁_eq]; simpa [ht_p'] using (hphi₁_all (lctVSize mem₀ nb cap)).1
        have hrk_eq : (AuxTree.node pp l r_old).rank (lctVSize st₁.mem nb cap) = t_p.rank (lctVSize mem₀ nb cap) := by
          unfold AuxTree.rank; rw [hperm_sz]
        exact htop_rk.trans hrk_eq
      have hdiff_hp : st₂.mem (nb - 1) - mem₀ (nb - 1) =
          (st₂.mem (nb - 1) - st₁.mem (nb - 1)) + (st₁.mem (nb - 1) - mem₀ (nb - 1)) := by
        have h1 : mem₀ (nb - 1) ≤ st₁.mem (nb - 1) := hfr₁.2.2.1
        have h2 : st₁.mem (nb - 1) ≤ st₂.mem (nb - 1) := by rw [← hhp_ptr]; exact hle_p
        omega
      let c_full : ℕ := (2 + c₁ + 1) +
          ((nodePtrExpr 0 6).size + 1 +
            ((fieldLoadExpr 7 OFF_RIGHT).size + 1 +
              (c_d +
                ((fieldAddrExpr 7 OFF_RIGHT).size + (Expr.reg 5).size + 1 +
                  ((nodePtrExpr 0 5).size + 1 +
                    ((fieldAddrExpr 8 OFF_PARENT).size + (Expr.reg 6).size + 1 +
                      ((fieldAddrExpr 8 OFF_PPAR).size + (Expr.const 0).size + 1 +
                        ((2 + c_p + 1) + ((Expr.reg 6).size + 1 + ((fieldLoadExpr 7 OFF_PPAR).size + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
      have hc_spl : c_full ≤ c₁ + c_p + 120 := by
        dsimp only [c_full]
        simp only [Expr.size, nodePtrExpr, fieldLoadExpr, fieldAddrExpr] at hc_d ⊢
        omega
      have hpot_total : c_full + 2 + (st₂.mem (nb - 1) - mem₀ (nb - 1)) + lctPhi L st₂.mem b n +
          (3 * K_SPLAY_STEP L + M_EXPOSE L) *
            (Nat.log 2 (n + 2) + 1 - t_next.rank (lctVSize st₂.mem nb cap)) ≤
          lctPhi L mem₀ b n +
            (3 * K_SPLAY_STEP L + M_EXPOSE L) *
              (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap)) := by
        have hrk_mono : t_y.rank (lctVSize mem₀ nb cap) ≤ t_next.rank (lctVSize st₂.mem nb cap) := by
          rw [htop_rk_tp]; exact hy_rk_le_tp
        have hlog_split : Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ nb cap) =
            (Nat.log 2 (n + 2) + 1 - t_next.rank (lctVSize st₂.mem nb cap)) +
              (t_next.rank (lctVSize st₂.mem nb cap) - t_y.rank (lctVSize mem₀ nb cap)) := by
          omega
        by_cases hhv : isHeavyRoot st₁.mem nb cap y = true
        · have hhv' := hhv_t hhv
          have hhc_mul : C_HEAVY L * lctHeavyCount st₂.mem nb cap + C_HEAVY L ≤
              C_HEAVY L * lctHeavyCount st₁.mem nb cap := by
            have h1 := Nat.mul_le_mul_left (C_HEAVY L) hhv'
            rwa [Nat.mul_add, Nat.mul_one] at h1
          have hphi_drop : lctPhi L st₂.mem b n + C_HEAVY L ≤ lctPhi L st₁.mem b n := by
            unfold lctPhi; rw [hphi_eq₂]; dsimp only [nb, cap] at hhc_mul; omega
          have hcancel := expose_heavy_cancel_le L
          have hmul_rk : 3 * K_SPLAY_STEP L * (t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap)) ≤
              (3 * K_SPLAY_STEP L + M_EXPOSE L) *
                (t_next.rank (lctVSize st₂.mem nb cap) - t_y.rank (lctVSize mem₀ nb cap)) := by
            rw [htop_rk_tp]
            exact Nat.mul_le_mul_right _ (by omega)
          rw [hlog_split, Nat.mul_add]
          rw [hhp_ptr] at hc_p
          omega
        · have hhv_f : isHeavyRoot st₁.mem nb cap y = false := Bool.eq_false_iff.2 hhv
          rcases hlt_f hhv_f with ⟨hhv_le, hrk_strict⟩
          have hhc_mul : C_HEAVY L * lctHeavyCount st₂.mem nb cap ≤
              C_HEAVY L * lctHeavyCount st₁.mem nb cap + C_HEAVY L := by
            have h1 := Nat.mul_le_mul_left (C_HEAVY L) hhv_le
            rwa [Nat.mul_add, Nat.mul_one] at h1
          have hphi_inc : lctPhi L st₂.mem b n ≤ lctPhi L st₁.mem b n + C_HEAVY L := by
            unfold lctPhi; rw [hphi_eq₂]; dsimp only [nb, cap] at hhc_mul; omega
          have hcancel := expose_light_le_M L
          have hrk_strict' : t_y.rank (lctVSize mem₀ nb cap) + 1 ≤ t_next.rank (lctVSize st₂.mem nb cap) := by
            rw [htop_rk]
            dsimp only [nb, cap] at *
            rw [← hvs₁_eq]
            exact hrk_strict
          have hdiff_ge : 1 ≤ t_next.rank (lctVSize st₂.mem nb cap) - t_y.rank (lctVSize mem₀ nb cap) := by omega
          have hmul_rk : 3 * K_SPLAY_STEP L * (t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap)) +
                M_EXPOSE L ≤
              (3 * K_SPLAY_STEP L + M_EXPOSE L) *
                (t_next.rank (lctVSize st₂.mem nb cap) - t_y.rank (lctVSize mem₀ nb cap)) := by
            rw [Nat.add_mul, htop_rk_tp]
            have h1 : M_EXPOSE L * 1 ≤ M_EXPOSE L * (t_p.rank (lctVSize mem₀ nb cap) - t_y.rank (lctVSize mem₀ nb cap)) :=
              Nat.mul_le_mul_left _ (by rw [← htop_rk_tp]; exact hdiff_ge)
            omega
          rw [hlog_split, Nat.mul_add]
          rw [hhp_ptr] at hc_p
          omega
      refine ⟨{ mem := st₂.mem, regs := Function.update r₅ 6 (nodeField st₂.mem nb pp OFF_PPAR), pos := st₂.pos },
        c_full, t_next, rest₂, hfull_run, hhi₂', hsafe₂, hfr_0_2, hpar_all, by simp [t_next],
        ?_, ?_, ?_, ?_, hlast_next, hsz_grow, hpot_total⟩
      · simp [r₅, r₉, hr₈_0]
      · simp [r₅, r₉, hr₈_1]
      · simp [r₅, AuxTree.rootId, t_next]
      · simp [AuxTree.rootId, t_next]

end MinCostFlow.LinkCut.Prog
