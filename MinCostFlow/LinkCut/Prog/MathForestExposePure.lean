module

public import MinCostFlow.LinkCut.Prog.MathForestExposeDefs

/-!
# Expose & Reroot Word-RAM Bodies and Pure Potential / Splice Lemmas

Defines `exposePhase1DetachStmt`, `exposeIterSpliceStmt`, `exposeBody`, and
`lctRerootBody` (with `NoRand`), plus pure preservation and Sleator–Tarjan rank/heavy-edge
lemmas (`lctAuxParent_mem_iff_of_trees`, `lctAux_detach_pure`, `lctAux_splice_pure`,
`lct_splice_rank_or_heavy`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PureStructuralHelpers

/-- Direct combined splice theorem for the `expose` loop: replaces right child `r_old` of
`.node p l r_old` with dashed child `t_y` (`ppar[t_y.rootId] = p`), preserving `lctAuxParent`,
`lctRepSize`, `splayMemPhi`, and `(.node p l t_y).treeSize = (.node p l r_old).treeSize`, while
satisfying the Sleator–Tarjan heavy/light dichotomy. -/
theorem lctAux_splice_pure {w h L : ℕ} {mem₀ mem₂ : ℕ → ℕ} {nb cap p : ℕ}
    {l r_old t_y : AuxTree} {rest : List AuxTree}
    (hok₀ : SplayForestOk w h L mem₀ nb cap (.node p l r_old :: t_y :: rest))
    (hacyc₀ : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem₀ nb cap) cap u = 0)
    (hpp_le₀ : nodeField mem₀ nb p OFF_PPAR ≤ cap ∧
      ∀ s ∈ rest, nodeField mem₀ nb s.rootId OFF_PPAR ≤ cap)
    (hrev0 : nodeField mem₀ nb p OFF_REV = 0)
    (hy_pp : nodeField mem₀ nb t_y.rootId OFF_PPAR = p)
    (hok₂ : SplayForestOk w h L mem₂ nb cap
      (match r_old with
       | .leaf => .node p l t_y :: rest
       | .node _ _ _ => .node p l t_y :: r_old :: rest))
    (hrest_agree : ∀ s ∈ rest,
      nodeField mem₂ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ nb) false = s.evalInorder (revFlag mem₀ nb) false)
    (hp_pp : nodeField mem₂ nb p OFF_PPAR = nodeField mem₀ nb p OFF_PPAR)
    (hp_eval : (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false =
      (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++ t_y.evalInorder (revFlag mem₀ nb) false)
    (hr_agree : match r_old with
      | .leaf => True
      | .node rc _ _ =>
          nodeField mem₂ nb rc OFF_PPAR = p ∧
          r_old.evalInorder (revFlag mem₂ nb) false = r_old.evalInorder (revFlag mem₀ nb) false) :
    (∀ u, lctAuxParent mem₂ nb cap u = lctAuxParent mem₀ nb cap u) ∧
    (∀ z, lctRepSize mem₂ nb cap z = lctRepSize mem₀ nb cap z) ∧
    t_y.treeSize (lctVSize mem₀ nb cap) ≤ lctVSize mem₀ nb cap p ∧
    (AuxTree.node p l t_y).treeSize (lctVSize mem₂ nb cap) =
      (AuxTree.node p l r_old).treeSize (lctVSize mem₀ nb cap) ∧
    (AuxTree.node p l t_y).rank (lctVSize mem₂ nb cap) =
      (AuxTree.node p l r_old).rank (lctVSize mem₀ nb cap) ∧
    splayMemPhi (K_SPLAY_STEP L) mem₂ nb cap (lctVSize mem₂ nb cap) =
      splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap (lctVSize mem₀ nb cap) ∧
    (isHeavyRoot mem₀ nb cap t_y.rootId = true →
      lctHeavyCount mem₂ nb cap + 1 ≤ lctHeavyCount mem₀ nb cap) ∧
    (isHeavyRoot mem₀ nb cap t_y.rootId = false →
      lctHeavyCount mem₂ nb cap ≤ lctHeavyCount mem₀ nb cap + 1 ∧
      t_y.rank (lctVSize mem₀ nb cap) + 1 ≤ (AuxTree.node p l r_old).rank (lctVSize mem₀ nb cap)) := by
  have hnd_all₀ : ((AuxTree.node p l r_old :: t_y :: rest).flatMap AuxTree.toList).Nodup :=
    hok₀.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hp_nd₀ : (AuxTree.node p l r_old).toList.Nodup := hnd_all₀.1
  have hy_ne : t_y ≠ .leaf := (hok₀.trees_ok t_y (by simp)).1
  have hp_b : 1 ≤ p ∧ p ≤ cap :=
    (hok₀.trees_ok (.node p l r_old) (by simp)).2.2.nodup_perm_mem (by simp [AuxTree.toList])
  have hrev_p0 : revFlag mem₀ nb p = false := by simp [revFlag, hrev0]
  have hp_seq₀ : (AuxTree.node p l r_old).evalInorder (revFlag mem₀ nb) false =
      (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++ r_old.evalInorder (revFlag mem₀ nb) false := by
    simp [AuxTree.evalInorder, hrev_p0]
  have hpp_le_all₀ : ∀ s ∈ (AuxTree.node p l r_old :: t_y :: rest),
      nodeField mem₀ nb s.rootId OFF_PPAR ≤ cap := by
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | hs_rest
    · exact hpp_le₀.1
    · rw [hy_pp]; exact hp_b.2
    · exact hpp_le₀.2 s hs_rest
  have hpp_le₂ : ∀ s ∈ (match r_old with
        | .leaf => AuxTree.node p l t_y :: rest
        | .node _ _ _ => AuxTree.node p l t_y :: r_old :: rest),
      nodeField mem₂ nb s.rootId OFF_PPAR ≤ cap := by
    cases r_old with
    | leaf =>
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs_rest
        · simpa [AuxTree.rootId, hp_pp] using hpp_le₀.1
        · rw [(hrest_agree s hs_rest).1]; exact hpp_le₀.2 s hs_rest
    | node rc rl rr =>
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | rfl | hs_rest
        · simpa [AuxTree.rootId, hp_pp] using hpp_le₀.1
        · simp only [AuxTree.rootId, hr_agree.1]; exact hp_b.2
        · rw [(hrest_agree s hs_rest).1]; exact hpp_le₀.2 s hs_rest
  have hpar_eq : ∀ u, lctAuxParent mem₂ nb cap u = lctAuxParent mem₀ nb cap u := by
    intro u
    rw [lctAuxParent_mem_iff_of_trees hok₂ hpp_le₂ u,
        lctAuxParent_mem_iff_of_trees hok₀ hpp_le_all₀ u]
    have htail_eq :
        rest.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem₂ nb) false
          if u ∈ seq then some (listParentFrom (nodeField mem₂ nb s.rootId OFF_PPAR) seq u) else none) =
        rest.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem₀ nb) false
          if u ∈ seq then some (listParentFrom (nodeField mem₀ nb s.rootId OFF_PPAR) seq u) else none) := by
      apply findSome?_congr_left
      intro s hs
      rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
      simp only [hpp_s, hseq_s]
    let seqL := l.evalInorder (revFlag mem₀ nb) false ++ [p]
    let seqY := t_y.evalInorder (revFlag mem₀ nb) false
    have hdisj_LY : ∀ a ∈ seqL, ∀ b ∈ seqY, a ≠ b := by
      intro a ha b hb
      have ha' : a ∈ (AuxTree.node p l r_old).toList := by
        simp only [seqL, List.mem_append, List.mem_singleton] at ha
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
        rcases ha with hl | rfl
        · exact Or.inl (Or.inl ((l.evalInorder_perm _ _).mem_iff.1 hl))
        · exact Or.inl (Or.inr rfl)
      have hb' : b ∈ t_y.toList := (t_y.evalInorder_perm _ _).mem_iff.1 hb
      exact hnd_all₀.2.2 a ha' b (List.mem_append.2 (Or.inl hb'))
    have hlastL : seqL.getLast? = some p := by simp [seqL]
    have happ_LY := listParentFrom_append_eq (prev := nodeField mem₀ nb p OFF_PPAR)
      (u := u) hlastL hdisj_LY
    dsimp only [seqL, seqY] at happ_LY
    cases r_old with
    | leaf =>
        have hp_seq₀' : (AuxTree.node p l .leaf).evalInorder (revFlag mem₀ nb) false = seqL := by
          simp [AuxTree.evalInorder, hrev_p0, seqL]
        by_cases huL : u ∈ seqL
        · have hu2 : u ∈ (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false := by
            rw [hp_eval]; exact List.mem_append.2 (Or.inl huL)
          have hu0 : u ∈ (AuxTree.node p l .leaf).evalInorder (revFlag mem₀ nb) false := by
            rw [hp_seq₀']; exact huL
          dsimp only [seqL] at huL
          rw [findSome?_cons_if hu2, findSome?_cons_if hu0]
          simp only [auxTree_rootId_node, hp_pp, hp_eval, hp_seq₀', happ_LY, huL, ↓reduceIte]
          rfl
        · by_cases huY : u ∈ t_y.evalInorder (revFlag mem₀ nb) false
          · have hu2 : u ∈ (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false := by
              rw [hp_eval]; exact List.mem_append.2 (Or.inr huY)
            have hu0 : u ∉ (AuxTree.node p l .leaf).evalInorder (revFlag mem₀ nb) false := by
              rw [hp_seq₀']; exact huL
            dsimp only [seqL] at huL
            rw [findSome?_cons_if hu2, findSome?_cons_if_neg hu0, findSome?_cons_if huY]
            simp only [auxTree_rootId_node, hp_pp, hp_eval, happ_LY, huL, ↓reduceIte, hy_pp]
          · have hu2 : u ∉ (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false := by
              rw [hp_eval, List.mem_append]; rintro (h | h) <;> contradiction
            have hu0 : u ∉ (AuxTree.node p l .leaf).evalInorder (revFlag mem₀ nb) false := by
              rw [hp_seq₀']; exact huL
            rw [findSome?_cons_if_neg hu2, findSome?_cons_if_neg hu0, findSome?_cons_if_neg huY, htail_eq]
    | node rc rl rr =>
        let seqR := (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false
        have hdisj_LR : ∀ a ∈ seqL, ∀ b ∈ seqR, a ≠ b := by
          intro a ha b hb
          have ha' : a ∈ l.toList ++ [p] := by
            simp only [seqL, List.mem_append, List.mem_singleton] at ha
            simp only [List.mem_append, List.mem_singleton]
            rcases ha with hl | rfl
            · exact Or.inl ((l.evalInorder_perm _ _).mem_iff.1 hl)
            · exact Or.inr rfl
          have hb' : b ∈ (AuxTree.node rc rl rr).toList :=
            ((AuxTree.node rc rl rr).evalInorder_perm _ _).mem_iff.1 hb
          have hx_nd' := hp_nd₀
          rw [AuxTree.toList, List.nodup_append] at hx_nd'
          exact hx_nd'.2.2 a ha' b hb'
        have happ_LR := listParentFrom_append_eq (prev := nodeField mem₀ nb p OFF_PPAR)
          (u := u) hlastL hdisj_LR
        dsimp only [seqL, seqR] at happ_LR
        by_cases huL : u ∈ l.evalInorder (revFlag mem₀ nb) false ++ [p]
        · have hu2 : u ∈ (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false := by
            rw [hp_eval]; exact List.mem_append.2 (Or.inl huL)
          have hu0 : u ∈ (AuxTree.node p l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false := by
            rw [hp_seq₀]; exact List.mem_append.2 (Or.inl huL)
          rw [findSome?_cons_if hu2, findSome?_cons_if hu0]
          simp only [auxTree_rootId_node, hp_pp, hp_eval, hp_seq₀, happ_LY, happ_LR, huL, ↓reduceIte]
        · by_cases huY : u ∈ t_y.evalInorder (revFlag mem₀ nb) false
          · have hu2 : u ∈ (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false := by
              rw [hp_eval]; exact List.mem_append.2 (Or.inr huY)
            have huR : u ∉ (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false := fun hr => by
              rw [hr_agree.2] at hr
              have hb_t : u ∈ (AuxTree.node p l (.node rc rl rr)).toList := by
                have hu_rc := ((AuxTree.node rc rl rr).evalInorder_perm _ _).mem_iff.1 hr
                rw [AuxTree.toList, List.mem_append]
                exact Or.inr hu_rc
              have hy_u : u ∈ t_y.toList := (t_y.evalInorder_perm _ _).mem_iff.1 huY
              exact hnd_all₀.2.2 u hb_t u (List.mem_append.2 (Or.inl hy_u)) rfl
            have hu0 : u ∉ (AuxTree.node p l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false := by
              rw [hp_seq₀, List.mem_append]
              rintro (h | h)
              · exact huL h
              · exact huR (by rw [hr_agree.2]; exact h)
            rw [findSome?_cons_if hu2, findSome?_cons_if_neg hu0, findSome?_cons_if huY]
            simp only [auxTree_rootId_node, hp_pp, hp_eval, happ_LY, huL, ↓reduceIte, hy_pp]
          · by_cases huR : u ∈ (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false
            · have hu2 : u ∉ (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false := by
                rw [hp_eval, List.mem_append]; rintro (h | h) <;> contradiction
              have hu2r : u ∈ (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false := by
                rw [hr_agree.2]; exact huR
              have hu0 : u ∈ (AuxTree.node p l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false := by
                rw [hp_seq₀]; exact List.mem_append.2 (Or.inr huR)
              rw [findSome?_cons_if_neg hu2, findSome?_cons_if hu2r, findSome?_cons_if hu0]
              simp only [auxTree_rootId_node, hr_agree.1, hr_agree.2, hp_seq₀, happ_LR, huL, ↓reduceIte]
            · have hu2 : u ∉ (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false := by
                rw [hp_eval, List.mem_append]; rintro (h | h) <;> contradiction
              have hu2r : u ∉ (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false := by
                rw [hr_agree.2]; exact huR
              have hu0 : u ∉ (AuxTree.node p l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false := by
                rw [hp_seq₀, List.mem_append]; rintro (h | h) <;> contradiction
              rw [findSome?_cons_if_neg hu2, findSome?_cons_if_neg hu2r, findSome?_cons_if_neg hu0,
                findSome?_cons_if_neg huY, htail_eq]
  have hrep_eq : ∀ z, lctRepSize mem₂ nb cap z = lctRepSize mem₀ nb cap z := by
    intro z; simp only [lctRepSize]; congr 1; apply List.filter_congr; intro u _
    have hiter : ∀ k q, iterParent (lctAuxParent mem₂ nb cap) k q =
        iterParent (lctAuxParent mem₀ nb cap) k q := by
      intro k; induction k with
      | zero => intro q; rfl
      | succ k ih => intro q; simp only [iterParent, hpar_eq, ih]
    simp only [reachesIn, hiter]
  have hacyc₂ : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem₂ nb cap) cap u = 0 := by
    intro u hu1 hu2
    have hiter : ∀ k q, iterParent (lctAuxParent mem₂ nb cap) k q =
        iterParent (lctAuxParent mem₀ nb cap) k q := by
      intro k; induction k with
      | zero => intro q; rfl
      | succ k ih => intro q; simp only [iterParent, hpar_eq, ih]
    rw [hiter]; exact hacyc₀ u hu1 hu2
  have hne₀ : ∀ s ∈ (AuxTree.node p l r_old :: t_y :: rest), lctTreeSeq mem₀ nb cap s.rootId ≠ [] :=
    fun s hs => by
      rw [hok₀.lctTreeSeq_eq hs]; exact auxTree_eval_ne_nil_of_ne_leaf (hok₀.trees_ok s hs).1
  have hy_sz : dashedChildSize mem₀ nb cap t_y.rootId = t_y.treeSize (lctVSize mem₀ nb cap) := by
    have htree := treeSize_lctVSize_eq_repSize hok₀ hacyc₀ hpp_le_all₀ hne₀ (t := t_y) (by simp)
    cases hcons : lctTreeSeq mem₀ nb cap t_y.rootId with
    | nil => exact absurd hcons (hne₀ t_y (by simp))
    | cons hd tl =>
        simp only [dashedChildSize, hcons]
        simpa [hcons] using htree.symm
  have hp_seq_eq₀ : lctTreeSeq mem₀ nb cap p =
      (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++ r_old.evalInorder (revFlag mem₀ nb) false := by
    have heq := hok₀.lctTreeSeq_eq (t := AuxTree.node p l r_old) (by simp)
    simpa [AuxTree.rootId, hp_seq₀] using heq
  have hp_seq_eq₂ : lctTreeSeq mem₂ nb cap p =
      (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++ t_y.evalInorder (revFlag mem₀ nb) false := by
    have heq := hok₂.lctTreeSeq_eq (t := AuxTree.node p l t_y) (by cases r_old <;> simp)
    simpa [AuxTree.rootId, hp_eval] using heq
  have hdcs_p : dashedChildSize mem₂ nb cap p = dashedChildSize mem₀ nb cap p := by
    simp only [dashedChildSize, hp_seq_eq₂, hp_seq_eq₀]
    cases l.evalInorder (revFlag mem₀ nb) false <;> simp [hrep_eq]
  have hheavy_p : isHeavyRoot mem₂ nb cap p = isHeavyRoot mem₀ nb cap p := by
    simp only [isHeavyRoot, hp_pp, hp_seq_eq₂, hp_seq_eq₀]
    cases l.evalInorder (revFlag mem₀ nb) false <;> simp [hrep_eq]
  have hperm₀ := hok₀.auxRootIds_perm
  have hperm₂ := hok₂.auxRootIds_perm
  have hy_le : t_y.treeSize (lctVSize mem₀ nb cap) ≤ lctVSize mem₀ nb cap p := by
    let contrib := fun q =>
      if nodeField mem₀ nb q OFF_PPAR = p then dashedChildSize mem₀ nb cap q else 0
    have hsf : (((auxRootIds mem₀ nb cap).filter (fun q => decide (nodeField mem₀ nb q OFF_PPAR = p))).map
        (dashedChildSize mem₀ nb cap)).sum =
        ((auxRootIds mem₀ nb cap).map contrib).sum := by
      simpa [contrib, decide_eq_true_eq] using
        list_filter_map_sum_ite (auxRootIds mem₀ nb cap)
          (fun q => decide (nodeField mem₀ nb q OFF_PPAR = p)) (dashedChildSize mem₀ nb cap)
    dsimp only [lctVSize]
    rw [hsf, (hperm₀.map contrib).sum_eq]
    have hy_in : t_y.rootId ∈ (AuxTree.node p l r_old :: t_y :: rest).map AuxTree.rootId := by simp
    have hmem : contrib t_y.rootId ≤ (((AuxTree.node p l r_old :: t_y :: rest).map AuxTree.rootId).map contrib).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨t_y.rootId, hy_in, rfl⟩)
    simpa [List.map_map, contrib, hy_pp, hy_sz] using hmem
  have hvs_eq : ∀ z, lctVSize mem₂ nb cap z +
      (if z = p then t_y.treeSize (lctVSize mem₀ nb cap) else 0) =
      lctVSize mem₀ nb cap z +
      (if z = p then (if r_old = .leaf then 0 else r_old.treeSize (lctVSize mem₀ nb cap)) else 0) := by
    have hz_ne : ∀ z, z ≠ p → lctVSize mem₂ nb cap z = lctVSize mem₀ nb cap z := by
      intro z hzp
      let contribZ := fun mem q =>
        if nodeField mem nb q OFF_PPAR = z then dashedChildSize mem nb cap q else 0
      have hsf : ∀ mem (rs : List ℕ),
          ((rs.filter fun q => decide (nodeField mem nb q OFF_PPAR = z)).map
            fun q => dashedChildSize mem nb cap q).sum = (rs.map (contribZ mem)).sum := fun mem rs => by
        simpa [contribZ, decide_eq_true_eq] using
          list_filter_map_sum_ite rs (fun q => decide (nodeField mem nb q OFF_PPAR = z))
            (dashedChildSize mem nb cap)
      simp only [lctVSize, hsf]
      rw [(hperm₂.map (contribZ mem₂)).sum_eq, (hperm₀.map (contribZ mem₀)).sum_eq]
      have htailZ : (rest.map AuxTree.rootId).map (contribZ mem₂) =
          (rest.map AuxTree.rootId).map (contribZ mem₀) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro s hs
        rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
        have htree_eq : lctTreeSeq mem₂ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
          rw [hok₂.lctTreeSeq_eq (by cases r_old <;> simp [hs]), hok₀.lctTreeSeq_eq (by simp [hs]), hseq_s]
        have hdcs_s : dashedChildSize mem₂ nb cap s.rootId = dashedChildSize mem₀ nb cap s.rootId := by
          simp only [dashedChildSize, htree_eq]
          cases lctTreeSeq mem₀ nb cap s.rootId with
          | nil => rfl
          | cons hd _ => simp [hrep_eq]
        simp [contribZ, hpp_s, hdcs_s]
      have hc_p : contribZ mem₂ p = contribZ mem₀ p := by simp [contribZ, hp_pp, hdcs_p]
      have hc_y : contribZ mem₀ t_y.rootId = 0 := by simp [contribZ, hy_pp, hzp.symm]
      cases r_old with
      | leaf =>
          simp only [List.map_cons, auxTree_rootId_node, List.sum_cons]
          rw [hc_p, hc_y, htailZ, Nat.zero_add]
      | node rc rl rr =>
          simp only [List.map_cons, auxTree_rootId_node, List.sum_cons]
          have hc_rc : contribZ mem₂ rc = 0 := by simp [contribZ, hr_agree.1, hzp.symm]
          rw [hc_p, hc_y, hc_rc, htailZ]
    intro z
    by_cases hzp : z = p
    · subst z
      simp only [↓reduceIte]
      let contribP := fun mem q =>
        if nodeField mem nb q OFF_PPAR = p then dashedChildSize mem nb cap q else 0
      have hsf : ∀ mem (rs : List ℕ),
          ((rs.filter fun q => decide (nodeField mem nb q OFF_PPAR = p)).map
            fun q => dashedChildSize mem nb cap q).sum = (rs.map (contribP mem)).sum := fun mem rs => by
        simpa [contribP, decide_eq_true_eq] using
          list_filter_map_sum_ite rs (fun q => decide (nodeField mem nb q OFF_PPAR = p))
            (dashedChildSize mem nb cap)
      simp only [lctVSize, hsf]
      rw [(hperm₂.map (contribP mem₂)).sum_eq, (hperm₀.map (contribP mem₀)).sum_eq]
      have htailP : (rest.map AuxTree.rootId).map (contribP mem₂) =
          (rest.map AuxTree.rootId).map (contribP mem₀) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro s hs
        rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
        have htree_eq : lctTreeSeq mem₂ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
          rw [hok₂.lctTreeSeq_eq (by cases r_old <;> simp [hs]), hok₀.lctTreeSeq_eq (by simp [hs]), hseq_s]
        have hdcs_s : dashedChildSize mem₂ nb cap s.rootId = dashedChildSize mem₀ nb cap s.rootId := by
          simp only [dashedChildSize, htree_eq]
          cases lctTreeSeq mem₀ nb cap s.rootId with
          | nil => rfl
          | cons hd _ => simp [hrep_eq]
        simp [contribP, hpp_s, hdcs_s]
      have hc_p : contribP mem₂ p = contribP mem₀ p := by dsimp only [contribP]; rw [hp_pp, hdcs_p]
      have hc_y : contribP mem₀ t_y.rootId = t_y.treeSize (lctVSize mem₀ nb cap) := by
        simp [contribP, hy_pp, hy_sz]
      cases r_old with
      | leaf =>
          simp only [↓reduceIte, Nat.add_zero, List.map_cons, auxTree_rootId_node, List.sum_cons]
          rw [hc_p, hc_y, htailP]; omega
      | node rc rl rr =>
          have hnot : (AuxTree.node rc rl rr = AuxTree.leaf) = False := by simp
          simp only [hnot, ↓reduceIte, List.map_cons, auxTree_rootId_node, List.sum_cons]
          have hne₂ : ∀ s ∈ (AuxTree.node p l t_y :: AuxTree.node rc rl rr :: rest),
              lctTreeSeq mem₂ nb cap s.rootId ≠ [] := fun s hs => by
            rw [hok₂.lctTreeSeq_eq hs]
            exact auxTree_eval_ne_nil_of_ne_leaf (hok₂.trees_ok s hs).1
          have hrc_sz : dashedChildSize mem₂ nb cap rc =
              (AuxTree.node rc rl rr).treeSize (lctVSize mem₂ nb cap) := by
            have htree := treeSize_lctVSize_eq_repSize hok₂ hacyc₂ hpp_le₂ hne₂
              (t := AuxTree.node rc rl rr) (by simp)
            simp only [AuxTree.rootId] at htree
            cases hcons : lctTreeSeq mem₂ nb cap rc with
            | nil => exact absurd hcons (by simpa [AuxTree.rootId] using hne₂ (.node rc rl rr) (by simp))
            | cons hd tl =>
                simp only [dashedChildSize, hcons]
                simpa [hcons] using htree.symm
          have hp_nin_r : p ∉ (AuxTree.node rc rl rr).toList := auxTree_nodup_id_nin_right hp_nd₀
          have hrc_sz₀ : (AuxTree.node rc rl rr).treeSize (lctVSize mem₂ nb cap) =
              (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) := by
            rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
            congr 1; apply List.map_congr_left
            intro u hu; exact congrArg (1 + ·) (hz_ne u (fun h => hp_nin_r (h ▸ hu)))
          have hc_rc : contribP mem₂ rc = (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) := by
            simp only [contribP, hr_agree.1, ↓reduceIte, hrc_sz, hrc_sz₀]
          rw [hc_p, hc_y, hc_rc, htailP]; omega
    · simp only [hzp, ↓reduceIte]; exact hz_ne z hzp
  have hz_eq_of_ne : ∀ z, z ≠ p → lctVSize mem₂ nb cap z = lctVSize mem₀ nb cap z := fun z hzp => by
    have := hvs_eq z; simp only [hzp, ↓reduceIte, Nat.add_zero] at this; exact this
  have hp_nin_l : p ∉ l.toList := auxTree_nodup_id_nin_left hp_nd₀
  have hp_nin_y : p ∉ t_y.toList := fun hm =>
    hnd_all₀.2.2 p (by simp [AuxTree.toList]) p (List.mem_append.2 (Or.inl hm)) rfl
  have hl_sz : l.treeSize (lctVSize mem₂ nb cap) = l.treeSize (lctVSize mem₀ nb cap) := by
    rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
    congr 1; apply List.map_congr_left
    intro u hu; exact congrArg (1 + ·) (hz_eq_of_ne u (fun h => hp_nin_l (h ▸ hu)))
  have hy_sz2 : t_y.treeSize (lctVSize mem₂ nb cap) = t_y.treeSize (lctVSize mem₀ nb cap) := by
    rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
    congr 1; apply List.map_congr_left
    intro u hu; exact congrArg (1 + ·) (hz_eq_of_ne u (fun h => hp_nin_y (h ▸ hu)))
  have htop_sz : (AuxTree.node p l t_y).treeSize (lctVSize mem₂ nb cap) =
      (AuxTree.node p l r_old).treeSize (lctVSize mem₀ nb cap) := by
    have hvp := hvs_eq p
    simp only [↓reduceIte] at hvp
    cases r_old with
    | leaf =>
        rw [show (if AuxTree.leaf = AuxTree.leaf then 0 else AuxTree.leaf.treeSize (lctVSize mem₀ nb cap)) = 0
          from by simp] at hvp
        simp only [AuxTree.treeSize, hl_sz, hy_sz2, Nat.add_zero] at hvp ⊢; omega
    | node rc rl rr =>
        rw [show (if AuxTree.node rc rl rr = AuxTree.leaf then 0
            else (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap)) =
            (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) from by simp] at hvp
        simp only [AuxTree.treeSize, hl_sz, hy_sz2] at hvp ⊢; omega
  have htop_rk : (AuxTree.node p l t_y).rank (lctVSize mem₂ nb cap) =
      (AuxTree.node p l r_old).rank (lctVSize mem₀ nb cap) := by
    simp only [AuxTree.rank, htop_sz]
  have hphi_eq : splayMemPhi (K_SPLAY_STEP L) mem₂ nb cap (lctVSize mem₂ nb cap) =
      splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap (lctVSize mem₀ nb cap) := by
    rw [splayMemPhi_eq_sum hok₂, splayMemPhi_eq_sum hok₀]
    have hsum_rest : (rest.map (AuxTree.treePhi (lctVSize mem₂ nb cap))).sum =
        (rest.map (AuxTree.treePhi (lctVSize mem₀ nb cap))).sum := by
      congr 1; apply List.map_congr_left; intro s hs
      exact auxTree_treePhi_congr fun u hu => hz_eq_of_ne u fun h => by
        rw [h] at hu
        exact hnd_all₀.2.2 p (by simp [AuxTree.toList]) p
          (List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨s, hs, hu⟩))) rfl
    have hl_phi : l.treePhi (lctVSize mem₂ nb cap) = l.treePhi (lctVSize mem₀ nb cap) :=
      auxTree_treePhi_congr fun u hu => hz_eq_of_ne u (fun h => hp_nin_l (h ▸ hu))
    have hy_phi : t_y.treePhi (lctVSize mem₂ nb cap) = t_y.treePhi (lctVSize mem₀ nb cap) :=
      auxTree_treePhi_congr fun u hu => hz_eq_of_ne u (fun h => hp_nin_y (h ▸ hu))
    cases r_old with
    | leaf =>
        simp only [List.map_cons, List.sum_cons]
        have htop_phi : (AuxTree.node p l t_y).treePhi (lctVSize mem₂ nb cap) =
            (AuxTree.node p l AuxTree.leaf).rank (lctVSize mem₀ nb cap) +
              l.treePhi (lctVSize mem₀ nb cap) + t_y.treePhi (lctVSize mem₀ nb cap) := by
          simp only [AuxTree.treePhi, AuxTree.rank, htop_sz, hl_phi, hy_phi]
        rw [htop_phi, hsum_rest]
        simp only [AuxTree.treePhi, AuxTree.rank, Nat.add_zero]
        ring
    | node rc rl rr =>
        have hp_nin_r : p ∉ (AuxTree.node rc rl rr).toList := auxTree_nodup_id_nin_right hp_nd₀
        have hr_phi : (AuxTree.node rc rl rr).treePhi (lctVSize mem₂ nb cap) =
            (AuxTree.node rc rl rr).treePhi (lctVSize mem₀ nb cap) :=
          auxTree_treePhi_congr fun u hu => hz_eq_of_ne u (fun h => hp_nin_r (h ▸ hu))
        simp only [List.map_cons, List.sum_cons]
        have htop_phi : (AuxTree.node p l t_y).treePhi (lctVSize mem₂ nb cap) =
            (AuxTree.node p l (AuxTree.node rc rl rr)).rank (lctVSize mem₀ nb cap) +
              l.treePhi (lctVSize mem₀ nb cap) + t_y.treePhi (lctVSize mem₀ nb cap) := by
          simp only [AuxTree.treePhi, AuxTree.rank, htop_sz, hl_phi, hy_phi]
        rw [htop_phi, hr_phi, hsum_rest]
        simp only [AuxTree.treePhi, AuxTree.rank]
        ring
  have hheavy_bal : lctHeavyCount mem₂ nb cap +
      (if isHeavyRoot mem₀ nb cap t_y.rootId then 1 else 0) =
      lctHeavyCount mem₀ nb cap +
        (match r_old with
         | .leaf => 0
         | .node rc _ _ => if isHeavyRoot mem₂ nb cap rc then 1 else 0) := by
    let hflag := fun mem q => if isHeavyRoot mem nb cap q then 1 else 0
    have hsf : ∀ mem (rs : List ℕ),
        (rs.filter (fun q => isHeavyRoot mem nb cap q)).length = (rs.map (hflag mem)).sum :=
      fun mem rs => list_filter_length_ite rs (isHeavyRoot mem nb cap)
    simp only [lctHeavyCount, hsf]
    rw [(hperm₂.map (hflag mem₂)).sum_eq, (hperm₀.map (hflag mem₀)).sum_eq]
    have htail : (rest.map AuxTree.rootId).map (hflag mem₂) =
        (rest.map AuxTree.rootId).map (hflag mem₀) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro s hs
      rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
      have htree_eq : lctTreeSeq mem₂ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
        rw [hok₂.lctTreeSeq_eq (by cases r_old <;> simp [hs]), hok₀.lctTreeSeq_eq (by simp [hs]), hseq_s]
      have hhs : isHeavyRoot mem₂ nb cap s.rootId = isHeavyRoot mem₀ nb cap s.rootId := by
        simp only [isHeavyRoot, hpp_s, htree_eq]
        cases lctTreeSeq mem₀ nb cap s.rootId with
        | nil => rfl
        | cons hd _ => simp [hrep_eq]
      simp only [Function.comp_def, hflag, hhs]
    have hhp : hflag mem₂ p = hflag mem₀ p := by simp only [hflag, hheavy_p]
    cases r_old with
    | leaf =>
        simp only [List.map_cons, auxTree_rootId_node, List.sum_cons]
        rw [hhp, htail]; dsimp only [hflag]; omega
    | node rc rl rr =>
        simp only [List.map_cons, auxTree_rootId_node, List.sum_cons]
        rw [hhp, htail]; dsimp only [hflag]; omega
  -- Size relationship with `lctRepSize mem₀ nb cap p` for heavy/light dichotomy
  have hy_head_sz : ∃ hy_hd, (lctTreeSeq mem₀ nb cap t_y.rootId).head? = some hy_hd ∧
      lctRepSize mem₀ nb cap hy_hd = t_y.treeSize (lctVSize mem₀ nb cap) := by
    rcases List.ne_nil_iff_exists_cons.1 (hne₀ t_y (by simp)) with ⟨hd, tl, hcons⟩
    exact ⟨hd, by simp [hcons], by simpa [dashedChildSize, hcons] using hy_sz⟩
  rcases hy_head_sz with ⟨hy_hd, hy_hd_eq, hy_rep_sz⟩
  have hheavy_y_iff : isHeavyRoot mem₀ nb cap t_y.rootId = true ↔
      lctRepSize mem₀ nb cap p < 2 * t_y.treeSize (lctVSize mem₀ nb cap) := by
    simp only [isHeavyRoot, hy_pp, Bool.and_eq_true, decide_eq_true_eq]
    have hp_cond : 1 ≤ p ∧ p ≤ cap := hp_b
    rcases List.ne_nil_iff_exists_cons.1 (hne₀ t_y (by simp)) with ⟨hd, tl, hcons⟩
    have hhd_eq : hd = hy_hd := by simp [hcons] at hy_hd_eq; exact hy_hd_eq
    subst hhd_eq
    simp [hcons, hp_cond, hy_rep_sz]
  have hp_rep_le_tree : lctRepSize mem₀ nb cap p ≤
      (AuxTree.node p l r_old).treeSize (lctVSize mem₀ nb cap) := by
    have htree := treeSize_lctVSize_eq_repSize hok₀ hacyc₀ hpp_le_all₀ hne₀
      (t := AuxTree.node p l r_old) (by simp)
    have hp_in_seq : p ∈ lctTreeSeq mem₀ nb cap (AuxTree.node p l r_old).rootId := by
      simp only [auxTree_rootId_node, hp_seq_eq₀]; simp
    rcases List.getElem_of_mem hp_in_seq with ⟨idx, hidx, hidx_eq⟩
    have hle := lctRepSize_ge_of_tree_idx hok₀ hacyc₀ hpp_le_all₀ (t := AuxTree.node p l r_old)
      (by simp) idx hidx
    rw [hidx_eq] at hle
    have hhd0 : (lctTreeSeq mem₀ nb cap (AuxTree.node p l r_old).rootId)[0] =
        (lctTreeSeq mem₀ nb cap (AuxTree.node p l r_old).rootId).head
          (hne₀ (AuxTree.node p l r_old) (by simp)) := by
      rw [List.head_eq_getElem_zero]
    rw [hhd0, ← htree] at hle
    exact hle
  have hy_sz_pos : 1 ≤ t_y.treeSize (lctVSize mem₀ nb cap) := by
    cases t_y with
    | leaf => exact absurd rfl hy_ne
    | node => simp [AuxTree.treeSize]; omega
  refine ⟨hpar_eq, hrep_eq, hy_le, htop_sz, htop_rk, hphi_eq, ?_, ?_⟩
  · intro hvy_true
    have hlt_y : lctRepSize mem₀ nb cap p < 2 * t_y.treeSize (lctVSize mem₀ nb cap) :=
      hheavy_y_iff.1 hvy_true
    cases r_old with
    | leaf =>
        simp only [hvy_true, ↓reduceIte, Nat.add_zero] at hheavy_bal
        omega
    | node rc rl rr =>
        have hpar_le : ∀ x, 1 ≤ x → x ≤ cap → lctAuxParent mem₀ nb cap x ≤ cap :=
          fun x _ _ => lctAuxParent_le_cap mem₀ nb cap x
        have hall_nd : ((List.range cap).map (· + 1)).Nodup :=
          List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)
        let cs := ((List.range cap).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem₀ nb cap c = p))
        have hcs_nd : cs.Nodup := hall_nd.filter _
        have hpar_y_hd : lctAuxParent mem₀ nb cap hy_hd = p := by
          have hp0 := lctAuxParent_of_tree hok₀ hpp_le_all₀ (t := t_y) (by simp) 0
            (List.length_pos_of_ne_nil (hne₀ t_y (by simp)))
          rcases List.ne_nil_iff_exists_cons.1 (hne₀ t_y (by simp)) with ⟨hd, tl, hcons⟩
          have hhd_eq : hd = hy_hd := by simp [hcons] at hy_hd_eq; exact hy_hd_eq
          subst hhd_eq
          simpa [hcons, hy_pp] using hp0
        have hy_hd_b : 1 ≤ hy_hd ∧ hy_hd ≤ cap := by
          have hm : hy_hd ∈ t_y.evalInorder (revFlag mem₀ nb) false := by
            rw [← hok₀.lctTreeSeq_eq (by simp)]
            exact List.mem_of_head? hy_hd_eq
          exact (hok₀.trees_ok t_y (by simp)).2.2.nodup_perm_mem
            ((t_y.evalInorder_perm _ _).mem_iff.1 hm)
        have hy_in_cs : hy_hd ∈ cs := by
          simp only [cs, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
          exact ⟨⟨hy_hd - 1, by omega, by omega⟩, hpar_y_hd⟩
        have hne₂ : ∀ s ∈ (AuxTree.node p l t_y :: AuxTree.node rc rl rr :: rest),
            lctTreeSeq mem₂ nb cap s.rootId ≠ [] := fun s hs => by
          rw [hok₂.lctTreeSeq_eq hs]; exact auxTree_eval_ne_nil_of_ne_leaf (hok₂.trees_ok s hs).1
        have hr_seq_ne : lctTreeSeq mem₂ nb cap rc ≠ [] := hne₂ (.node rc rl rr) (by simp)
        rcases List.ne_nil_iff_exists_cons.1 hr_seq_ne with ⟨r_hd, r_tl, hr_cons⟩
        have hr_rep_sz : lctRepSize mem₀ nb cap r_hd =
            (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) := by
          have htree := treeSize_lctVSize_eq_repSize hok₂ hacyc₂ hpp_le₂ hne₂
            (t := AuxTree.node rc rl rr) (by simp)
          have hr_sz0 : (AuxTree.node rc rl rr).treeSize (lctVSize mem₂ nb cap) =
              (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) := by
            rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
            congr 1; apply List.map_congr_left
            intro u hu
            have hp_nin_r : p ∉ (AuxTree.node rc rl rr).toList := auxTree_nodup_id_nin_right hp_nd₀
            exact congrArg (1 + ·) (hz_eq_of_ne u (fun h => hp_nin_r (h ▸ hu)))
          simp only [AuxTree.rootId] at htree
          rw [← hr_sz0]
          have hhd_eq : (lctTreeSeq mem₂ nb cap rc).head hr_seq_ne = r_hd := by simp [hr_cons]
          rw [← hrep_eq r_hd, ← hhd_eq, ← htree]
        have hr_seq2 : (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false = r_hd :: r_tl := by
          have hseq := hok₂.lctTreeSeq_eq (t := AuxTree.node rc rl rr) (by simp)
          simp only [AuxTree.rootId] at hseq
          rw [← hseq, hr_cons]
        have hr_hd_eq0 : lctTreeSeq mem₀ nb cap p =
            (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++ r_hd :: r_tl := by
          calc
            lctTreeSeq mem₀ nb cap p
              = (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++
                  (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false := hp_seq_eq₀
            _ = (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++
                  (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false := by rw [hr_agree.2]
            _ = (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++ r_hd :: r_tl := by rw [hr_seq2]
        have hpar_r_hd : lctAuxParent mem₀ nb cap r_hd = p := by
          let j := (l.evalInorder (revFlag mem₀ nb) false).length
          have hj1 : j + 1 < (lctTreeSeq mem₀ nb cap (AuxTree.node p l (.node rc rl rr)).rootId).length := by
            simp only [auxTree_rootId_node, hr_hd_eq0]; simp [j]
          have hp0 := lctAuxParent_of_tree hok₀ hpp_le_all₀
            (t := AuxTree.node p l (.node rc rl rr)) (by simp) (j + 1) hj1
          have hget_j1 : (lctTreeSeq mem₀ nb cap p)[j + 1]? = some r_hd := by
            rw [hr_hd_eq0]; simp [j, List.append_assoc]
          have hj1_p : j + 1 < (lctTreeSeq mem₀ nb cap p).length := by
            simpa [auxTree_rootId_node] using hj1
          have hget_j1' : (lctTreeSeq mem₀ nb cap p)[j + 1] = r_hd := by
            rw [List.getElem?_eq_getElem hj1_p] at hget_j1
            exact Option.some.inj hget_j1
          have hget_j : (lctTreeSeq mem₀ nb cap p)[j]! = p := by
            rw [hr_hd_eq0]; simp [j, List.append_assoc]
          simp only [auxTree_rootId_node] at hp0
          simpa [hget_j1', hget_j] using hp0
        have hr_hd_b : 1 ≤ r_hd ∧ r_hd ≤ cap := by
          have hm : r_hd ∈ (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false := by
            rw [hr_seq2]; simp
          have hm0 : r_hd ∈ (AuxTree.node rc rl rr).toList :=
            ((AuxTree.node rc rl rr).evalInorder_perm _ _).mem_iff.1 hm
          have hm_t : r_hd ∈ (AuxTree.node p l (.node rc rl rr)).toList := by
            rw [AuxTree.toList, List.mem_append]
            exact Or.inr hm0
          exact (hok₀.trees_ok (.node p l (.node rc rl rr)) (by simp)).2.2.nodup_perm_mem hm_t
        have hr_in_cs : r_hd ∈ cs := by
          simp only [cs, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
          exact ⟨⟨r_hd - 1, by omega, by omega⟩, hpar_r_hd⟩
        have hne_hy_r : hy_hd ≠ r_hd := fun heq => by
          have hm1 : hy_hd ∈ t_y.toList := by
            have hmt : hy_hd ∈ t_y.evalInorder (revFlag mem₀ nb) false := by
              rw [← hok₀.lctTreeSeq_eq (by simp)]; exact List.mem_of_head? hy_hd_eq
            exact (t_y.evalInorder_perm _ _).mem_iff.1 hmt
          have hm2 : r_hd ∈ (AuxTree.node rc rl rr).toList := by
            have hm : r_hd ∈ (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false := by
              rw [hr_seq2]; simp
            exact ((AuxTree.node rc rl rr).evalInorder_perm _ _).mem_iff.1 hm
          have hm_t : r_hd ∈ (AuxTree.node p l (.node rc rl rr)).toList := by
            rw [AuxTree.toList, List.mem_append]
            exact Or.inr hm2
          exact hnd_all₀.2.2 r_hd hm_t r_hd (List.mem_append.2 (Or.inl (heq ▸ hm1))) rfl
        have hsum_two := list_sum_two_mem_le hcs_nd (lctRepSize mem₀ nb cap) hy_in_cs hr_in_cs hne_hy_r
        have hrep_p := lctRepSize_eq_one_add_sum mem₀ nb cap p hpar_le hacyc₀ hp_b.1 hp_b.2
        have hsum_bound : t_y.treeSize (lctVSize mem₀ nb cap) +
            (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) < lctRepSize mem₀ nb cap p := by
          rw [← hy_rep_sz, ← hr_rep_sz, hrep_p]; dsimp only [cs] at hsum_two; omega
        have hnot_heavy_r : isHeavyRoot mem₂ nb cap rc = false := by
          simp only [isHeavyRoot, Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not,
            hr_agree.1, hr_cons, hrep_eq, hr_rep_sz]
          right; omega
        simp only [hvy_true, ↓reduceIte, hnot_heavy_r, Bool.false_eq_true] at hheavy_bal
        omega
  · intro hvy_false
    have hle_y : 2 * t_y.treeSize (lctVSize mem₀ nb cap) ≤ lctRepSize mem₀ nb cap p := by
      by_contra hlt
      exact absurd (hheavy_y_iff.2 (by omega)) (by simp [hvy_false])
    have hcount_le : lctHeavyCount mem₂ nb cap ≤ lctHeavyCount mem₀ nb cap + 1 := by
      cases r_old with
      | leaf => simp only [hvy_false] at hheavy_bal; omega
      | node rc rl rr =>
          simp only [hvy_false] at hheavy_bal
          split_ifs at hheavy_bal <;> omega
    refine ⟨hcount_le, ?_⟩
    unfold AuxTree.rank
    exact nat_log2_two_mul_le hy_sz_pos (le_trans hle_y hp_rep_le_tree)

end PureStructuralHelpers

end MinCostFlow.LinkCut.Prog
