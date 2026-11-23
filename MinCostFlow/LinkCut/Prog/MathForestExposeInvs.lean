module

public import MinCostFlow.LinkCut.Prog.MathForestExposeInvsBase

/-!
# Expose Invariant Bundle and Operation Preservation

Defines `LctExposeInvs` (header, `SplayForestOk`, free-slot chain, vertex/edge slots,
`LctAuxPathOk`, `LctSubdivOk`) and proves preservation under `splay` (`LctExposeInvs.of_splay`),
`exposePhase1DetachStmt` (`LctExposeInvs.of_detach`), and `exposeIterSpliceStmt`
(`LctExposeInvs.of_splice`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section DetachAndSplicePreservation

theorem LctExposeInvs.of_splice {w h L P b n v : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {p : ℕ} {l r_old t_y : AuxTree} {rest : List AuxTree}
    {mem₀ mem₂ : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (.node p l r_old :: t_y :: rest) mem₀)
    (hrev0 : nodeField mem₀ (lctNodesBase b) p OFF_REV = 0)
    (hht0 : nodeField mem₀ (lctNodesBase b) p OFF_HAS_TAG = 0)
    (hy_pp : nodeField mem₀ (lctNodesBase b) t_y.rootId OFF_PPAR = p)
    (hy_last : (t_y.evalInorder (revFlag mem₀ (lctNodesBase b)) false).getLast? = some (v + 1))
    (hv : v < n)
    (hhp₂ : mem₂ (lctNodesBase b - 1) < 2 ^ w)
    (hpp : nodeField mem₂ (lctNodesBase b) p OFF_PPAR =
      nodeField mem₀ (lctNodesBase b) p OFF_PPAR)
    (htree_p : TreeMemMatch w h L mem₂ (lctNodesBase b) (lctCap n) (.node p l t_y) 0
      (nodeField mem₂ (lctNodesBase b) p OFF_PPAR))
    (hl_fields : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₀ (lctNodesBase b) u off)
    (hy_fields : ∀ u ∈ t_y.toList, ∀ off < NODE_STRIDE,
      (u = t_y.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₀ (lctNodesBase b) u off)
    (hnonAgg_p : ∀ off < NODE_STRIDE,
      off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
      off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
      off ≠ OFF_RIGHT →
      nodeField mem₂ (lctNodesBase b) p off = nodeField mem₀ (lctNodesBase b) p off)
    (hl : ∀ u ≤ lctCap n, u ∉ (AuxTree.node p l t_y).toList → ∀ off < NODE_STRIDE,
      (r_old ≠ .leaf → u = r_old.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₀ (lctNodesBase b) u off)
    (hr_par : r_old ≠ .leaf → nodeField mem₂ (lctNodesBase b) r_old.rootId OFF_PARENT = 0)
    (hr_pp : r_old ≠ .leaf → nodeField mem₂ (lctNodesBase b) r_old.rootId OFF_PPAR = p)
    (hfr : LctFrame (lctNodesBase b + NODE_STRIDE)
      (lctNodesBase b + NODE_STRIDE * (lctCap n + 1)) (lctNodesBase b - 1) mem₀ mem₂) :
    let nb := lctNodesBase b
    let cap := lctCap n
    let trees₂ := if r_old = .leaf then .node p l t_y :: rest else .node p l t_y :: r_old :: rest
    LctExposeInvs w h L P b n freeEdges edgeMap trees₂ mem₂ ∧
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
  intro nb cap trees₂
  have hsf_rep : SplayForestOk w h L mem₂ nb cap trees₂ ∧
      (∀ s ∈ rest, nodeField mem₂ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
        s.evalInorder (revFlag mem₂ nb) false = s.evalInorder (revFlag mem₀ nb) false) ∧
      (∀ rc rl rr, r_old = .node rc rl rr →
        nodeField mem₂ nb rc OFF_PPAR = p ∧
        r_old.evalInorder (revFlag mem₂ nb) false = r_old.evalInorder (revFlag mem₀ nb) false) := by
    cases r_old with
    | leaf =>
        rcases splayForestOk_reparent_splice hi.sf hhp₂ hpp htree_p hl hr_par hr_pp hfr with
          ⟨hsf2, hra, _⟩
        exact ⟨by simpa [trees₂] using hsf2, hra, fun _ _ _ h => by cases h⟩
    | node rc rl rr =>
        rcases splayForestOk_reparent_splice hi.sf hhp₂ hpp htree_p hl hr_par hr_pp hfr with
          ⟨hsf2, hra, hrg⟩
        exact ⟨by simpa [trees₂] using hsf2, hra, by rintro _ _ _ ⟨rfl⟩; exact hrg⟩
  rcases hsf_rep with ⟨hsf₂, hrest_agree, hr_agree⟩
  have hhdr := lctFrame_hdr_eq hfr
  have hnd_all₀ : ((AuxTree.node p l r_old :: t_y :: rest).flatMap AuxTree.toList).Nodup :=
    hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hp_nd₀ := hnd_all₀.1
  have hy_nd₀ := hnd_all₀.2.1.1
  have hp_tok := hi.sf.trees_ok (.node p l r_old) (by simp)
  have hy_tok := hi.sf.trees_ok t_y (by simp)
  have hrev2 : nodeField mem₂ nb p OFF_REV = 0 := by
    rw [hnonAgg_p OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hrev0
  have hht2 : nodeField mem₂ nb p OFF_HAS_TAG = 0 := by
    rw [hnonAgg_p OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hht0
  have hrev_p2 : revFlag mem₂ nb p = false := by simp [revFlag, nb, hrev2]
  have hl_eval : l.evalInorder (revFlag mem₂ nb) false = l.evalInorder (revFlag mem₀ nb) false := by
    apply AuxTree.evalInorder_agree
    intro u hu; simp only [revFlag, nb, hl_fields u hu OFF_REV (by decide)]
  have hy_eval : t_y.evalInorder (revFlag mem₂ nb) false = t_y.evalInorder (revFlag mem₀ nb) false := by
    apply AuxTree.evalInorder_agree
    intro u hu; simp only [revFlag, nb, hy_fields u hu OFF_REV (by decide) (fun _ => ⟨by decide, by decide⟩)]
  have hp_eval : (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false =
      (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++ t_y.evalInorder (revFlag mem₀ nb) false := by
    simp only [AuxTree.evalInorder, hrev_p2, hl_eval, hy_eval, List.append_assoc]
  have hpp_le₀ : nodeField mem₀ nb p OFF_PPAR ≤ cap ∧
      ∀ s ∈ rest, nodeField mem₀ nb s.rootId OFF_PPAR ≤ cap :=
    ⟨hi.ppar_le_cap (.node p l r_old) (by simp), fun s hs => hi.ppar_le_cap s (by simp [hs])⟩
  have hpure : (∀ u, lctAuxParent mem₂ nb cap u = lctAuxParent mem₀ nb cap u) ∧
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
    cases r_old with
    | leaf =>
        have hsf2 : SplayForestOk w h L mem₂ nb cap (.node p l t_y :: rest) := by
          simpa [trees₂] using hsf₂
        exact lctAux_splice_pure hi.sf hi.subdivOk.1 hpp_le₀ hrev0 hy_pp hsf2 hrest_agree hpp hp_eval trivial
    | node rc rl rr =>
        have hsf2 : SplayForestOk w h L mem₂ nb cap (.node p l t_y :: .node rc rl rr :: rest) := by
          simpa [trees₂] using hsf₂
        exact lctAux_splice_pure hi.sf hi.subdivOk.1 hpp_le₀ hrev0 hy_pp hsf2 hrest_agree hpp hp_eval
          (hr_agree rc rl rr rfl)
  rcases hpure with ⟨hpar_eq, hrep_eq, hy_le, htop_sz, htop_rk, hphi_eq, hheavy_t, hlight_f⟩
  have hp_nin_free : p ∉ freeEdges := fun hpm => by
    have hy_aux := (hi.auxPathOk t_y (by simp)).2.1
    rw [hy_pp] at hy_aux
    rcases hy_aux with hp0 | ⟨_, _, hnin⟩
    · have hp1 := (hp_tok.2.2.nodup_perm_mem (y := p) (by simp [AuxTree.toList])).1; omega
    · exact hnin hpm
  have hy_ne : t_y ≠ .leaf := hy_tok.1
  have hy_nin_free : t_y.rootId ∉ freeEdges := fun hym => by
    rcases (hi.freeNodeOk t_y.rootId hym).2.2.2 with ⟨hpp0, _⟩
    have hp1 := (hp_tok.2.2.nodup_perm_mem (y := p) (by simp [AuxTree.toList])).1
    omega
  have hfree_not_in_heads : ∀ ed ∈ freeEdges,
      ed ∉ (AuxTree.node p l r_old).toList ∧ ed ∉ t_y.toList := by
    intro ed hed
    rcases hi.freeNodeOk ed hed with ⟨_, _, htr, _, _, _⟩
    simp only [List.mem_cons] at htr
    rcases htr with heq | heq | hrest
    · have hed_eq : ed = p := congrArg AuxTree.rootId heq
      exact absurd (hed_eq ▸ hed) hp_nin_free
    · have hed_eq : ed = t_y.rootId := congrArg AuxTree.rootId heq
      exact absurd (hed_eq ▸ hed) hy_nin_free
    · constructor
      · intro hm
        exact hnd_all₀.2.2 ed hm ed (List.mem_append.2 (Or.inr
          (List.mem_flatMap.2 ⟨_, hrest, by simp [AuxTree.toList]⟩))) rfl
      · intro hm
        exact hnd_all₀.2.1.2.2 ed hm ed (List.mem_flatMap.2 ⟨_, hrest, by simp [AuxTree.toList]⟩) rfl
  have hfreeChain₂ : FreeSlotChain mem₂ nb (mem₂ (b + LCT_HDR_FREE)) freeEdges := by
    rw [hhdr.2.2.1]
    exact freeSlotChain_agree_of_eu hi.freeChain fun ed hed => by
      have he_ok := hi.freeNodeOk ed hed
      have hnin := hfree_not_in_heads ed hed
      have hnin_pt : ed ∉ (AuxTree.node p l t_y).toList := by
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
        rintro ((h | rfl) | h)
        · exact hnin.1 (by simp [AuxTree.toList, h])
        · exact hp_nin_free hed
        · exact hnin.2 h
      have hne_r : r_old ≠ .leaf → ed ≠ r_old.rootId := fun hr heq =>
        hnin.1 (by rw [heq]; simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
      exact hl ed he_ok.2.1 hnin_pt OFF_EU (by decide) (fun hr heq => absurd heq (hne_r hr))
  have hfreeNode₂ : ∀ ed ∈ freeEdges, n + 1 ≤ ed ∧ ed ≤ cap ∧
      AuxTree.node ed .leaf .leaf ∈ trees₂ ∧
      nodeField mem₂ nb ed OFF_PPAR = 0 ∧
      nodeField mem₂ nb ed OFF_ISV = 0 ∧
      nodeField mem₂ nb ed OFF_HASE = 0 := by
    intro ed hed
    rcases hi.freeNodeOk ed hed with ⟨h1, h2, htr, hpp_ed, hisv, hhe⟩
    have htr_rest : AuxTree.node ed .leaf .leaf ∈ rest := by
      simp only [List.mem_cons] at htr
      rcases htr with heq | heq | hrest
      · have hed_eq : ed = p := congrArg AuxTree.rootId heq
        exact absurd (hed_eq ▸ hed) hp_nin_free
      · have hed_eq : ed = t_y.rootId := congrArg AuxTree.rootId heq
        exact absurd (hed_eq ▸ hed) hy_nin_free
      · exact hrest
    have htr₂ : AuxTree.node ed .leaf .leaf ∈ trees₂ := by cases r_old <;> simp [trees₂, htr_rest]
    have hnin := hfree_not_in_heads ed hed
    have hnin_pt : ed ∉ (AuxTree.node p l t_y).toList := by
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
      rintro ((h | rfl) | h)
      · exact hnin.1 (by simp [AuxTree.toList, h])
      · exact hp_nin_free hed
      · exact hnin.2 h
    have hne_r : r_old ≠ .leaf → ed ≠ r_old.rootId := fun hr heq =>
      hnin.1 (by rw [heq]; simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
    refine ⟨h1, h2, htr₂, ?_, ?_, ?_⟩
    · rw [hl ed h2 hnin_pt OFF_PPAR (by decide) (fun hr heq => absurd heq (hne_r hr))]; exact hpp_ed
    · rw [hl ed h2 hnin_pt OFF_ISV (by decide) (fun hr heq => absurd heq (hne_r hr))]; exact hisv
    · rw [hl ed h2 hnin_pt OFF_HASE (by decide) (fun hr heq => absurd heq (hne_r hr))]; exact hhe
  have hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nb - 1) → mem₂ a = mem₀ a :=
    fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)
  have hvert₂ : VertexNodeOk mem₂ nb n := by
    intro u hu
    have hcap_def : lctCap n = 2 * n := rfl
    have hu_le : u + 1 ≤ cap := by dsimp only [cap]; omega
    have hof : ∀ off, (off = OFF_ISV ∨ off = OFF_HASE) →
        nodeField mem₂ nb (u + 1) off = nodeField mem₀ nb (u + 1) off := by
      intro off hoff
      by_cases hup : u + 1 = p
      · rw [hup]
        rcases hoff with rfl | rfl <;>
          exact hnonAgg_p _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · by_cases hul : u + 1 ∈ l.toList
        · rcases hoff with rfl | rfl <;> exact hl_fields _ hul _ (by decide)
        · by_cases huy : u + 1 ∈ t_y.toList
          · exact hy_fields _ huy off (by rcases hoff with rfl | rfl <;> decide)
              (fun _ => by rcases hoff with rfl | rfl <;> exact ⟨by decide, by decide⟩)
          · have hnin : u + 1 ∉ (AuxTree.node p l t_y).toList := by
              simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
              rintro ((h | h) | h)
              · exact hul h
              · exact hup h
              · exact huy h
            exact hl (u + 1) hu_le hnin off (by rcases hoff with rfl | rfl <;> decide)
              (fun _ _ => by rcases hoff with rfl | rfl <;> exact ⟨by decide, by decide⟩)
    exact ⟨by rw [hof OFF_ISV (Or.inl rfl)]; exact (hi.vertexOk u hu).1,
      by rw [hof OFF_HASE (Or.inr rfl)]; exact (hi.vertexOk u hu).2⟩
  have hl_steps : evalMemSteps mem₂ nb h L l false 0 = evalMemSteps mem₀ nb h L l false 0 :=
    evalMemSteps_agree_of_nonStruct hp_tok.2.2.children_match.1 (auxTree_nodup_left hp_nd₀)
      (fun u hu off hoff _ => hl_fields u hu off hoff) hheap false 0
  have hy_steps : evalMemSteps mem₂ nb h L t_y false 0 = evalMemSteps mem₀ nb h L t_y false 0 :=
    evalMemSteps_agree_of_nonStruct hy_tok.2.2 hy_nd₀ hy_fields hheap false 0
  have hown_p : nodeOwnRawStep mem₂ nb h L p = nodeOwnRawStep mem₀ nb h L p :=
    nodeOwnRawStep_agree_of_nonAgg hp_tok.2.2 (fun off hlt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _ _ =>
      hnonAgg_p off hlt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) hheap
  have hr_steps : evalMemSteps mem₂ nb h L r_old false 0 = evalMemSteps mem₀ nb h L r_old false 0 := by
    have hdisj_pt_r : ∀ a ∈ (AuxTree.node p l t_y).toList, ∀ b ∈ r_old.toList, a ≠ b := by
      intro a ha b hb
      have hp_nd' := hp_nd₀
      rw [AuxTree.toList, List.nodup_append] at hp_nd'
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at ha
      rcases ha with (hl' | rfl) | hy'
      · exact hp_nd'.2.2 a (List.mem_append.2 (Or.inl hl')) b hb
      · exact hp_nd'.2.2 a (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))) b hb
      · exact (hnd_all₀.2.2 b (by simp [AuxTree.toList, hb]) a (List.mem_append.2 (Or.inl hy'))).symm
    exact evalMemSteps_agree_of_nonStruct hp_tok.2.2.children_match.2 (auxTree_nodup_right hp_nd₀)
      (fun u hu off hoff hne => hl u (hp_tok.2.2.children_match.2.nodup_perm_mem hu).2
        (fun hm => hdisj_pt_r u hm u hu rfl) off hoff (fun _ h => hne h))
      hheap false 0
  have hsplit₀ : evalMemSteps mem₀ nb h L (.node p l r_old) false 0 =
      evalMemSteps mem₀ nb h L l false 0 ++
        ((nodeOwnRawStep mem₀ nb h L p).map (fun s => s.addDeltaMod h L 0)).toList ++
        evalMemSteps mem₀ nb h L r_old false 0 :=
    evalMemSteps_split_of_root_zero (by simp [nb, revFlag, hrev0]) hht0
  have hsplit₂ : evalMemSteps mem₂ nb h L (.node p l t_y) false 0 =
      (evalMemSteps mem₀ nb h L l false 0 ++
        ((nodeOwnRawStep mem₀ nb h L p).map (fun s => s.addDeltaMod h L 0)).toList) ++
        evalMemSteps mem₀ nb h L t_y false 0 := by
    rw [evalMemSteps_split_of_root_zero hrev_p2 hht2, hl_steps, hown_p, hy_steps]
  have hedge₂ : ActiveEdgeNodeOk mem₂ nb h L P n trees₂ edgeMap := by
    intro q hq
    rcases hi.edgeOk q hq with ⟨h1, h2, hisv, hhe, heid, heu, hev_f, s_old, hs_old_mem,
      hed_in, st_old, hst_mem, hmatch, hdir_ok⟩
    have hst_id : st_old.nodeId = q.1 := hmatch.1
    have hq_fields : ∀ off, (off = OFF_ISV ∨ off = OFF_HASE ∨ off = OFF_EID ∨
        off = OFF_EU ∨ off = OFF_EV) →
        nodeField mem₂ nb q.1 off = nodeField mem₀ nb q.1 off := by
      intro off hoff
      by_cases hqp : q.1 = p
      · rw [hqp]
        rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
          exact hnonAgg_p _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · by_cases hql : q.1 ∈ l.toList
        · rcases hoff with rfl | rfl | rfl | rfl | rfl <;> exact hl_fields _ hql _ (by decide)
        · by_cases hqy : q.1 ∈ t_y.toList
          · exact hy_fields _ hqy off (by rcases hoff with rfl | rfl | rfl | rfl | rfl <;> decide)
              (fun _ => by rcases hoff with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
          · have hnin : q.1 ∉ (AuxTree.node p l t_y).toList := by
              simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
              rintro ((h | h) | h)
              · exact hql h
              · exact hqp h
              · exact hqy h
            exact hl q.1 h2 hnin off (by rcases hoff with rfl | rfl | rfl | rfl | rfl <;> decide)
              (fun _ _ => by rcases hoff with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
    refine ⟨h1, h2,
      by rw [hq_fields OFF_ISV (Or.inl rfl)]; exact hisv,
      by rw [hq_fields OFF_HASE (Or.inr (Or.inl rfl))]; exact hhe,
      by rw [hq_fields OFF_EID (Or.inr (Or.inr (Or.inl rfl)))]; exact heid,
      by rw [hq_fields OFF_EU (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact heu,
      by rw [hq_fields OFF_EV (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact hev_f, ?_⟩
    simp only [List.mem_cons] at hs_old_mem
    rcases hs_old_mem with rfl | hty | hs_rest
    · rw [hsplit₀, List.mem_append] at hst_mem
      rcases hst_mem with hsl_p | hsr
      · have hsl_2 : st_old ∈ evalMemSteps mem₂ nb h L (.node p l t_y) false 0 := by
          rw [hsplit₂]; exact List.mem_append.2 (Or.inl hsl_p)
        have hmem_t2 : AuxTree.node p l t_y ∈ trees₂ := by cases r_old <;> simp [trees₂]
        refine ⟨.node p l t_y, hmem_t2, hst_id ▸ evalMemSteps_nodeId_mem_toList hsl_2, st_old,
          hsl_2, hmatch, by simpa [nb, cap, hpar_eq] using hdir_ok⟩
      · cases hr_eq : r_old with
        | leaf => subst hr_eq; simp [evalMemSteps] at hsr
        | node rc rl rr =>
            have hsr' : st_old ∈ evalMemSteps mem₀ nb h L (AuxTree.node rc rl rr) false 0 := by
              rw [hr_eq] at hsr; exact hsr
            have hed_in_r : q.1 ∈ (AuxTree.node rc rl rr).toList :=
              hst_id ▸ evalMemSteps_nodeId_mem_toList hsr'
            have hmem_t2 : AuxTree.node rc rl rr ∈ trees₂ := by simp [trees₂, hr_eq]
            refine ⟨.node rc rl rr, hmem_t2, hed_in_r, st_old, ?_, hmatch, ?_⟩
            · rw [← hr_eq, hr_steps]; exact hsr
            · simpa [nb, cap, hpar_eq] using hdir_ok
    · subst hty
      have hsy_2 : st_old ∈ evalMemSteps mem₂ nb h L (.node p l s_old) false 0 := by
        rw [hsplit₂]; exact List.mem_append.2 (Or.inr hst_mem)
      have hmem_t2 : AuxTree.node p l s_old ∈ trees₂ := by cases r_old <;> simp [trees₂]
      refine ⟨.node p l s_old, hmem_t2, hst_id ▸ evalMemSteps_nodeId_mem_toList hsy_2, st_old,
        hsy_2, hmatch, by simpa [nb, cap, hpar_eq] using hdir_ok⟩
    · have hdisj_s : ∀ u ∈ s_old.toList, u ≤ cap ∧ u ∉ (AuxTree.node p l r_old).toList ∧
          u ∉ t_y.toList := fun u hu =>
        ⟨(hi.sf.trees_ok s_old (by simp [hs_rest])).2.2.nodup_perm_mem hu |>.2,
         fun hm => hnd_all₀.2.2 u hm u (List.mem_append.2 (Or.inr
           (List.mem_flatMap.2 ⟨s_old, hs_rest, hu⟩))) rfl,
         fun hm => hnd_all₀.2.1.2.2 u hm u (List.mem_flatMap.2 ⟨s_old, hs_rest, hu⟩) rfl⟩
      have hs_nd := list_nodup_of_flatMap_nodup hnd_all₀.2.1.2.1 hs_rest
      have hsteps_rest : evalMemSteps mem₂ nb h L s_old false 0 =
          evalMemSteps mem₀ nb h L s_old false 0 := by
        apply evalMemSteps_agree_of_nonStruct (hi.sf.trees_ok s_old (by simp [hs_rest])).2.2 hs_nd
        · intro u hu off hoff _
          rcases hdisj_s u hu with ⟨hb, hnp, hny⟩
          have hnr : r_old ≠ .leaf → u ≠ r_old.rootId := fun hr heq => by
            rw [heq] at hnp; exact hnp (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
          have hnx : u ∉ (AuxTree.node p l t_y).toList := fun hm => by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm
            rcases hm with (hl' | rfl) | hy'
            · exact hnp (by simp [AuxTree.toList, hl'])
            · exact hnp (by simp [AuxTree.toList])
            · exact hny hy'
          exact hl u hb hnx off hoff (fun hr heq => absurd heq (hnr hr))
        · exact hheap
      have hmem_t2 : s_old ∈ trees₂ := by cases r_old <;> simp [trees₂, hs_rest]
      refine ⟨s_old, hmem_t2, hed_in, st_old, by rw [hsteps_rest]; exact hst_mem, hmatch,
        by simpa [nb, cap, hpar_eq] using hdir_ok⟩
  have haux₂ : LctAuxPathOk mem₂ nb n freeEdges trees₂ := by
    have hok_pt : let seq := (AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false
        let pp_p := nodeField mem₂ nb p OFF_PPAR
        seq ≠ [] ∧ (pp_p = 0 ∨ (1 ≤ pp_p ∧ pp_p ≤ cap ∧ pp_p ∉ freeEdges)) ∧
        ((p ∈ freeEdges ∧ AuxTree.node p l t_y = .node p .leaf .leaf ∧ pp_p = 0) ∨
          (∃ u, u < n ∧ seq.getLast? = some (u + 1))) := by
      have h0 := hi.auxPathOk (.node p l r_old) (by simp)
      have hy_seq_ne : t_y.evalInorder (revFlag mem₀ nb) false ≠ [] :=
        auxTree_eval_ne_nil_of_ne_leaf hy_ne
      have hlast_pt : ((AuxTree.node p l t_y).evalInorder (revFlag mem₂ nb) false).getLast? =
          some (v + 1) := by
        rw [hp_eval, List.getLast?_append_of_ne_nil _ hy_seq_ne]
        exact hy_last
      dsimp only at h0 ⊢
      rw [hpp]
      exact ⟨by rw [hp_eval]; intro h; exact hy_seq_ne (List.append_eq_nil_iff.1 h).2, h0.2.1,
        Or.inr ⟨v, hv, hlast_pt⟩⟩
    cases hr_eq : r_old with
    | leaf =>
        intro s hs
        simp only [trees₂, hr_eq, ↓reduceIte, List.mem_cons] at hs
        rcases hs with rfl | hs_rest
        · exact hok_pt
        · have h0 := hi.auxPathOk s (by simp [hs_rest])
          rcases hrest_agree s hs_rest with ⟨hp_s, hev_s⟩
          dsimp only at h0 ⊢; rw [hp_s, hev_s]; exact h0
    | node rc rl rr =>
        intro s hs
        have hnot : (AuxTree.node rc rl rr = AuxTree.leaf) = False := by simp
        simp only [trees₂, hr_eq, hnot, ↓reduceIte, List.mem_cons] at hs
        rcases hs with rfl | rfl | hs_rest
        · exact hok_pt
        · have h0 := hi.auxPathOk (.node p l r_old) (by simp)
          have hrev_p0 : revFlag mem₀ nb p = false := by simp [revFlag, nb, hrev0]
          have hseq0 : (AuxTree.node p l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false =
              (l.evalInorder (revFlag mem₀ nb) false ++ [p]) ++
              (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false := by
            simp [AuxTree.evalInorder, hrev_p0]
          have hr_ne : AuxTree.node rc rl rr ≠ .leaf := by simp
          have hseq_r_ne : (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false ≠ [] :=
            auxTree_eval_ne_nil_of_ne_leaf hr_ne
          have hlast_eq : ((AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false).getLast? =
              ((AuxTree.node p l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false).getLast? := by
            rw [hseq0, List.getLast?_append_of_ne_nil _ hseq_r_ne]
          have hp_b := hp_tok.2.2.nodup_perm_mem (y := p) (by simp [AuxTree.toList])
          have hrg := hr_agree rc rl rr hr_eq
          rw [hr_eq] at h0 hrg
          dsimp only at h0 ⊢
          simp only [auxTree_rootId_node]
          rw [hrg.1, hrg.2]
          refine ⟨by simpa [hr_eq] using hseq_r_ne, Or.inr ⟨hp_b.1, hp_b.2, hp_nin_free⟩, ?_⟩
          rcases h0.2.2 with ⟨hp_in, _⟩ | ⟨u, hu, hlast⟩
          · exact absurd hp_in hp_nin_free
          · exact Or.inr ⟨u, hu, hlast_eq.trans (by simpa [hr_eq] using hlast)⟩
        · have h0 := hi.auxPathOk s (by simp [hs_rest])
          rcases hrest_agree s hs_rest with ⟨hp_s, hev_s⟩
          dsimp only at h0 ⊢; rw [hp_s, hev_s]; exact h0
  have hsub₂ := lctSubdivOk_of_par_eq hi.subdivOk hpar_eq
  exact ⟨⟨hhdr.1.trans hi.hdrN, hhdr.2.1.trans hi.hdrCap, hhdr.2.2.2.1.trans hi.hdrL,
    hhdr.2.2.2.2.trans hi.hdrP, hsf₂, hfreeChain₂, hfreeNode₂, hvert₂, hedge₂, haux₂, hsub₂⟩,
    hpar_eq, hrep_eq, hy_le, htop_sz, htop_rk, hphi_eq, hheavy_t, hlight_f⟩

end DetachAndSplicePreservation

end MinCostFlow.LinkCut.Prog
