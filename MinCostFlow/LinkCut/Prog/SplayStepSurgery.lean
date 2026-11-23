module

public import MinCostFlow.LinkCut.Prog.SplayStepEval

/-!
# Subtree surgery under the memory match

Facts about `AuxTree.replaceSubtree` and `TreeMemMatch`, among them
`AuxTree.replaceSubtree_preserves`.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

public section AuxTreeSurgery

theorem AuxTree.replaceSubtree_rootId {subId : ℕ} {s' t : AuxTree}
    (ht : t ≠ .leaf) (_hs' : s' ≠ .leaf) :
    (t.replaceSubtree subId s').rootId =
      if t.rootId = subId then s'.rootId else t.rootId := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r =>
      by_cases heq : id = subId <;> simp [replaceSubtree, rootId, heq]

theorem TreeMemMatch.child_ne_of_not_mem {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {q : AuxTree} {qp qpp subId : ℕ}
    (hq : TreeMemMatch w h L mem nodesBase cap q qp qpp)
    (hsub_pos : 1 ≤ subId) (hsub_nin : subId ∉ q.toList) :
    ∀ v ∈ q.toList,
      nodeField mem nodesBase v OFF_LEFT ≠ subId ∧
      nodeField mem nodesBase v OFF_RIGHT ≠ subId := by
  induction q generalizing qp qpp with
  | leaf => intro _ hv; simp [AuxTree.toList] at hv
  | node id l r ihl ihr =>
      rcases hq with ⟨_, _, hL, hR, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      have hnin_l : subId ∉ l.toList := fun h => hsub_nin (by simp [AuxTree.toList, h])
      have hnin_r : subId ∉ r.toList := fun h => hsub_nin (by simp [AuxTree.toList, h])
      intro v hv
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hv
      rcases hv with (hvl | rfl) | hvr
      · exact ihl hl hnin_l v hvl
      · constructor
        · intro heq
          rw [heq] at hL
          cases l with
          | leaf => simp [AuxTree.rootId] at hL; omega
          | node lid _ _ => simp [AuxTree.rootId] at hL; subst hL; exact hnin_l (by simp [AuxTree.toList])
        · intro heq
          rw [heq] at hR
          cases r with
          | leaf => simp [AuxTree.rootId] at hR; omega
          | node rid _ _ => simp [AuxTree.rootId] at hR; subst hR; exact hnin_r (by simp [AuxTree.toList])
      · exact ihr hr hnin_r v hvr

/-- Replacing `t.findSubtree subId` with `s'` preserves `TreeMemMatch` and logical sequences
across arbitrary outer reversal flags and tags whenever `s'` preserves `evalInorder`, `listVcnt`,
and `evalMemSteps ... false 0`. -/
theorem AuxTree.replaceSubtree_preserves {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    {t s' : AuxTree} {p₀ pp₀ subId : ℕ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap t p₀ pp₀)
    (hnd : t.toList.Nodup)
    (hsub : subId ∈ t.toList)
    (hs_match : TreeMemMatch w h L mem₂ nodesBase cap s' (t.parentIn subId p₀)
      (if t.rootId = subId then pp₀ else 0))
    (hs_ne : s' ≠ .leaf)
    (hs_perm : s'.toList.Perm (t.findSubtree subId).toList)
    (hs_eval : s'.evalInorder (revFlag mem₂ nodesBase) false =
      (t.findSubtree subId).evalInorder (revFlag mem₁ nodesBase) false)
    (hs_vcnt : listVcnt mem₂ nodesBase (s'.evalInorder (revFlag mem₂ nodesBase) false) =
      listVcnt mem₁ nodesBase ((t.findSubtree subId).evalInorder (revFlag mem₁ nodesBase) false))
    (hs_steps : evalMemSteps mem₂ nodesBase h L s' false 0 =
      evalMemSteps mem₁ nodesBase h L (t.findSubtree subId) false 0)
    (hhp : mem₁ (nodesBase - 1) ≤ mem₂ (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₁ (nodesBase - 1) →
      mem₂ a = mem₁ a)
    (houter_other : ∀ u ∈ t.toList, u ∉ (t.findSubtree subId).toList →
      ∀ off < NODE_STRIDE, off ≠ OFF_LEFT → off ≠ OFF_RIGHT →
        nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (houter_left : ∀ u ∈ t.toList, u ∉ (t.findSubtree subId).toList →
      nodeField mem₂ nodesBase u OFF_LEFT =
        if nodeField mem₁ nodesBase u OFF_LEFT = subId then s'.rootId
        else nodeField mem₁ nodesBase u OFF_LEFT)
    (houter_right : ∀ u ∈ t.toList, u ∉ (t.findSubtree subId).toList →
      nodeField mem₂ nodesBase u OFF_RIGHT =
        if nodeField mem₁ nodesBase u OFF_RIGHT = subId then s'.rootId
        else nodeField mem₁ nodesBase u OFF_RIGHT) :
    TreeMemMatch w h L mem₂ nodesBase cap (t.replaceSubtree subId s') p₀ pp₀ ∧
      (t.replaceSubtree subId s').toList.Perm t.toList ∧
      (t.replaceSubtree subId s').evalInorder (revFlag mem₂ nodesBase) false =
        t.evalInorder (revFlag mem₁ nodesBase) false ∧
      listVcnt mem₂ nodesBase ((t.replaceSubtree subId s').evalInorder (revFlag mem₂ nodesBase) false) =
        listVcnt mem₁ nodesBase (t.evalInorder (revFlag mem₁ nodesBase) false) ∧
      evalMemSteps mem₂ nodesBase h L (t.replaceSubtree subId s') false 0 =
        evalMemSteps mem₁ nodesBase h L t false 0 := by
  have hsub_pos : 1 ≤ subId := by
    have hm := AuxTree.findSubtree_match ht hsub
    rcases AuxTree.findSubtree_mem_toList hsub with ⟨_, hr⟩
    cases hs : t.findSubtree subId with
    | leaf => contradiction
    | node y _ _ => rw [hs] at hm hr; dsimp [AuxTree.rootId] at hr; subst hr; exact hm.1
  induction t generalizing p₀ pp₀ with
  | leaf => simp [AuxTree.toList] at hsub
  | node id l r ihl ihr =>
      simp only [AuxTree.replaceSubtree]
      by_cases heq : id = subId
      · subst heq
        simp only [AuxTree.findSubtree, AuxTree.parentIn, AuxTree.rootId, ↓reduceIte] at *
        exact ⟨hs_match, hs_perm, hs_eval, hs_vcnt, hs_steps⟩
      · simp only [heq, ↓reduceIte]
        have hnd' := hnd
        simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
          List.mem_singleton] at hnd'
        rcases hnd' with ⟨⟨hl_nd, _, hdisj_id_l⟩, hr_nd, hdisj_lr⟩
        have hid_mem : id ∈ (AuxTree.node id l r).toList := by simp [AuxTree.toList]
        have hnot_sub_id : id ∉ ((AuxTree.node id l r).findSubtree subId).toList := by
          intro hid
          simp only [AuxTree.findSubtree, heq, ↓reduceIte] at hid
          split_ifs at hid with hnl
          · exact hdisj_id_l id (AuxTree.findSubtree_subset hid) id rfl rfl
          · exact hdisj_lr id (Or.inr rfl) id (AuxTree.findSubtree_subset hid) rfl
        have heq_id := fun off hoff hL hR =>
          houter_other id hid_mem hnot_sub_id off hoff hL hR
        have hrev_id : revFlag mem₂ nodesBase id = revFlag mem₁ nodesBase id := by
          simp only [revFlag, heq_id OFF_REV (by decide) (by decide) (by decide)]
        rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, hr, hiv, hhe, hsum, hdir, hht, htn,
          heu, hev, heid, he1, he0, hcf, hcb, htag1, htag0, hm1h, hm2h, hm1_1, hm1_0,
          hagg, hl_m, hr_m⟩
        have heval_steps_branch : ∀ q,
            evalMemSteps mem₂ nodesBase h L (q.replaceSubtree subId s') false 0 =
              evalMemSteps mem₁ nodesBase h L q false 0 →
            TreeMemMatch w h L mem₂ nodesBase cap (q.replaceSubtree subId s') id 0 →
            TreeMemMatch w h L mem₁ nodesBase cap q id 0 →
            ∀ fl d,
              evalMemSteps mem₂ nodesBase h L (q.replaceSubtree subId s') fl d =
                evalMemSteps mem₁ nodesBase h L q fl d := by
          intro q hst0 hm2 hm1 fl d
          have hfl_eq : evalMemSteps mem₂ nodesBase h L (q.replaceSubtree subId s') fl 0 =
              evalMemSteps mem₁ nodesBase h L q fl 0 := by
            cases fl
            · exact hst0
            · rw [← neg_zero]
              rw [evalMemSteps_true_eq hm2 0, evalMemSteps_true_eq hm1 0, hst0]
          rw [← add_zero d, evalMemSteps_addDeltaMod hm2, evalMemSteps_addDeltaMod hm1, hfl_eq]
        have hown_id : nodeOwnRawStep mem₂ nodesBase h L id = nodeOwnRawStep mem₁ nodesBase h L id := by
          simp only [nodeOwnRawStep, heq_id OFF_HASE (by decide) (by decide) (by decide)]
          by_cases hhe_id : nodeField mem₁ nodesBase id OFF_HASE = 0
          · simp [hhe_id]
          · have hhe1 : nodeField mem₁ nodesBase id OFF_HASE = 1 := by omega
            rcases he1 hhe1 with ⟨pf, paf, pab, pcf, pcb, _⟩
            simp only [hhe_id, ↓reduceIte,
              heq_id OFF_DIR (by decide) (by decide) (by decide),
              heq_id OFF_EID (by decide) (by decide) (by decide),
              heq_id OFF_EU (by decide) (by decide) (by decide),
              heq_id OFF_EV (by decide) (by decide) (by decide),
              heq_id OFF_FLOW_PTR (by decide) (by decide) (by decide),
              heq_id OFF_AF_PTR (by decide) (by decide) (by decide),
              heq_id OFF_AB_PTR (by decide) (by decide) (by decide),
              heq_id OFF_COST_FWD (by decide) (by decide) (by decide),
              heq_id OFF_COST_BWD (by decide) (by decide) (by decide)]
            rw [intVal_agree_heap hheap pf.2.1 pf.2.2.1,
              intVal_agree_heap hheap paf.2.1 paf.2.2.1,
              intVal_agree_heap hheap pab.2.1 pab.2.2.1,
              intVal_agree_heap hheap pcf.2.1 pcf.2.2.1,
              intVal_agree_heap hheap pcb.2.1 pcb.2.2.1]
        have htag_id : nodeTagInt mem₂ nodesBase h L id = nodeTagInt mem₁ nodesBase h L id := by
          simp only [nodeTagInt, heq_id OFF_HAS_TAG (by decide) (by decide) (by decide)]
          by_cases hht_id : nodeField mem₁ nodesBase id OFF_HAS_TAG = 0
          · simp [hht_id]
          · have hht1 : nodeField mem₁ nodesBase id OFF_HAS_TAG = 1 := by omega
            rcases (htag1 hht1).1 with ⟨_, hlo, hhi, hval⟩
            simp only [hht_id, ↓reduceIte,
              heq_id OFF_TAG_NEG (by decide) (by decide) (by decide),
              heq_id OFF_TAG_PTR (by decide) (by decide) (by decide)]
            rw [optIntVal_agree_heap hheap (Or.inr ⟨hlo, hhi, hval⟩)]
        by_cases hnl : subId ∈ l.toList
        · have hnr : subId ∉ r.toList := fun hr_in => hdisj_lr subId (Or.inl hnl) subId hr_in rfl
          have hrep_r : r.replaceSubtree subId s' = r := AuxTree.replaceSubtree_not_mem hnr
          have hfind : (AuxTree.node id l r).findSubtree subId = l.findSubtree subId := by
            simp [AuxTree.findSubtree, heq, hnl]
          have hpar_l : (AuxTree.node id l r).parentIn subId p₀ = l.parentIn subId id := by
            simp [AuxTree.parentIn, heq, hnl]
          have hs_match_l : TreeMemMatch w h L mem₂ nodesBase cap s' (l.parentIn subId id)
              (if l.rootId = subId then 0 else 0) := by
            have h0 : (if l.rootId = subId then (0 : ℕ) else 0) = 0 := by split_ifs <;> rfl
            have hne_root : (AuxTree.node id l r).rootId ≠ subId := by simp [AuxTree.rootId, heq]
            simpa [hpar_l, hne_root, h0] using hs_match
          have hnot_in_r : ∀ u ∈ r.toList, u ∉ (l.findSubtree subId).toList := fun u hu hu_sub =>
            hdisj_lr u (Or.inl (AuxTree.findSubtree_subset hu_sub)) u hu rfl
          have hr_field_eq : ∀ u ∈ r.toList, ∀ off < NODE_STRIDE,
              nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off := by
            intro u hu off hoff
            have hu_mem : u ∈ (AuxTree.node id l r).toList := by simp [AuxTree.toList, hu]
            have hu_nsub : u ∉ ((AuxTree.node id l r).findSubtree subId).toList := by
              rw [hfind]; exact hnot_in_r u hu
            by_cases hOL : off = OFF_LEFT
            · subst hOL
              rw [houter_left u hu_mem hu_nsub]
              have hc := TreeMemMatch.child_ne_of_not_mem hr_m hsub_pos hnr u hu
              simp [hc.1]
            · by_cases hOR : off = OFF_RIGHT
              · subst hOR
                rw [houter_right u hu_mem hu_nsub]
                have hc := TreeMemMatch.child_ne_of_not_mem hr_m hsub_pos hnr u hu
                simp [hc.2]
              · exact houter_other u hu_mem hu_nsub off hoff hOL hOR
          have hr_m2 : TreeMemMatch w h L mem₂ nodesBase cap r id 0 :=
            memAgree_treeMemMatch_of_nodeList hr_m hr_field_eq hhp hheap
          have hr_steps_fl : ∀ fl d,
              evalMemSteps mem₂ nodesBase h L r fl d = evalMemSteps mem₁ nodesBase h L r fl d :=
            fun fl d => evalMemSteps_agree hr_m hr_field_eq hheap fl d
          have houter_l_other : ∀ u ∈ l.toList, u ∉ (l.findSubtree subId).toList →
              ∀ off < NODE_STRIDE, off ≠ OFF_LEFT → off ≠ OFF_RIGHT →
                nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off :=
            fun u hu hn => houter_other u (by simp [AuxTree.toList, hu]) (by rwa [hfind])
          have houter_l_left : ∀ u ∈ l.toList, u ∉ (l.findSubtree subId).toList →
              nodeField mem₂ nodesBase u OFF_LEFT =
                if nodeField mem₁ nodesBase u OFF_LEFT = subId then s'.rootId
                else nodeField mem₁ nodesBase u OFF_LEFT :=
            fun u hu hn => houter_left u (by simp [AuxTree.toList, hu]) (by rwa [hfind])
          have houter_l_right : ∀ u ∈ l.toList, u ∉ (l.findSubtree subId).toList →
              nodeField mem₂ nodesBase u OFF_RIGHT =
                if nodeField mem₁ nodesBase u OFF_RIGHT = subId then s'.rootId
                else nodeField mem₁ nodesBase u OFF_RIGHT :=
            fun u hu hn => houter_right u (by simp [AuxTree.toList, hu]) (by rwa [hfind])
          rcases ihl hl_m hl_nd hnl hs_match_l (by simpa [hfind] using hs_perm)
              (by simpa [hfind] using hs_eval) (by simpa [hfind] using hs_vcnt)
              (by simpa [hfind] using hs_steps)
              houter_l_other houter_l_left houter_l_right with
            ⟨hl_m2, hl_perm2, hl_eval2, hl_vcnt2, hl_steps2⟩
          have hl_eval_true : (l.replaceSubtree subId s').evalInorder (revFlag mem₂ nodesBase) true =
              l.evalInorder (revFlag mem₁ nodesBase) true := by
            rw [AuxTree.evalInorder_true, hl_eval2, AuxTree.evalInorder_true]
          have hr_eval_any : ∀ b, r.evalInorder (revFlag mem₂ nodesBase) b =
              r.evalInorder (revFlag mem₁ nodesBase) b :=
            fun b => AuxTree.evalInorder_agree _ _ r b fun u hu => by
              simp [revFlag, hr_field_eq u hu OFF_REV (by decide)]
          have heval_node : (AuxTree.node id (l.replaceSubtree subId s') r).evalInorder (revFlag mem₂ nodesBase) false =
              (AuxTree.node id l r).evalInorder (revFlag mem₁ nodesBase) false := by
            cases hrv : revFlag mem₁ nodesBase id <;>
              simp [AuxTree.evalInorder, hrev_id, hrv, hl_eval2, hl_eval_true, hr_eval_any]
          have hl_steps_fl := heval_steps_branch l hl_steps2 hl_m2 hl_m
          have hsteps_node : evalMemSteps mem₂ nodesBase h L (AuxTree.node id (l.replaceSubtree subId s') r) false 0 =
              evalMemSteps mem₁ nodesBase h L (AuxTree.node id l r) false 0 := by
            simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor,
              hown_id, htag_id, hrev_id, hl_steps_fl, hr_steps_fl]
          have hvc_node : listVcnt mem₂ nodesBase ((AuxTree.node id (l.replaceSubtree subId s') r).evalInorder (revFlag mem₂ nodesBase) false) =
              listVcnt mem₁ nodesBase ((AuxTree.node id l r).evalInorder (revFlag mem₁ nodesBase) false) := by
            have hl_vc_rev : listVcnt mem₂ nodesBase (l.evalInorder (revFlag mem₁ nodesBase) true) =
                listVcnt mem₁ nodesBase (l.evalInorder (revFlag mem₁ nodesBase) true) := by
              rw [AuxTree.evalInorder_true, listVcnt_reverse, listVcnt_reverse]
              rw [hl_eval2] at hl_vcnt2; exact hl_vcnt2
            have hr_vc : ∀ b, listVcnt mem₂ nodesBase (r.evalInorder (revFlag mem₁ nodesBase) b) =
                listVcnt mem₁ nodesBase (r.evalInorder (revFlag mem₁ nodesBase) b) := fun b => by
              apply listVcnt_agree_of_mem
              intro u hu
              have hu_r := (r.evalInorder_perm (revFlag mem₁ nodesBase) b).mem_iff.mp hu
              exact hr_field_eq u hu_r OFF_ISV (by decide)
            rw [heval_node]
            cases hrv : revFlag mem₁ nodesBase id <;>
              simp only [AuxTree.evalInorder, hrv, listVcnt_append, listVcnt,
                heq_id OFF_ISV (by decide) (by decide) (by decide)]
            · rw [hl_eval2] at hl_vcnt2; rw [hl_vcnt2, hr_vc false]
            · rw [hr_vc true, hl_vc_rev]
          have hroot_l : (l.replaceSubtree subId s').rootId =
              if l.rootId = subId then s'.rootId else l.rootId :=
            AuxTree.replaceSubtree_rootId (by cases l <;> simp_all [AuxTree.toList]) hs_ne
          have hL' : nodeField mem₂ nodesBase id OFF_LEFT = (l.replaceSubtree subId s').rootId := by
            rw [houter_left id hid_mem hnot_sub_id, hL, hroot_l]
          have hR' : nodeField mem₂ nodesBase id OFF_RIGHT = r.rootId := by
            rw [houter_right id hid_mem hnot_sub_id, hR]
            cases r with
            | leaf =>
                have : (0 : ℕ) ≠ subId := by omega
                simp [AuxTree.rootId, this]
            | node rid _ _ =>
                have : rid ≠ subId := fun he => hnr (he ▸ by simp [AuxTree.toList])
                simp [AuxTree.rootId, this]
          refine ⟨?_, ?_, by rw [hrep_r]; exact heval_node, by rw [hrep_r]; exact hvc_node,
            by rw [hrep_r]; exact hsteps_node⟩
          · rw [hrep_r]
            refine ⟨hx1, hx2, hL', hR', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hl_m2, hr_m2⟩
            · simpa [heq_id OFF_PARENT (by decide) (by decide) (by decide)] using hP
            · simpa [heq_id OFF_PPAR (by decide) (by decide) (by decide)] using hPP
            · simpa [heq_id OFF_REV (by decide) (by decide) (by decide)] using hr
            · simpa [heq_id OFF_ISV (by decide) (by decide) (by decide)] using hiv
            · simpa [heq_id OFF_HASE (by decide) (by decide) (by decide)] using hhe
            · simpa [heq_id OFF_ISV (by decide) (by decide) (by decide),
                heq_id OFF_HASE (by decide) (by decide) (by decide)] using hsum
            · simpa [heq_id OFF_DIR (by decide) (by decide) (by decide)] using hdir
            · simpa [heq_id OFF_HAS_TAG (by decide) (by decide) (by decide)] using hht
            · simpa [heq_id OFF_TAG_NEG (by decide) (by decide) (by decide)] using htn
            · simpa [heq_id OFF_EU (by decide) (by decide) (by decide)] using heu
            · simpa [heq_id OFF_EV (by decide) (by decide) (by decide)] using hev
            · simpa [heq_id OFF_EID (by decide) (by decide) (by decide)] using heid
            · intro hhe1
              rw [heq_id OFF_HASE (by decide) (by decide) (by decide)] at hhe1
              rcases he1 hhe1 with ⟨pf, paf, pab, pcf, pcb, hcb_eq⟩
              rw [heq_id OFF_FLOW_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AF_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AB_PTR (by decide) (by decide) (by decide),
                heq_id OFF_COST_FWD (by decide) (by decide) (by decide),
                heq_id OFF_COST_BWD (by decide) (by decide) (by decide)]
              refine ⟨numPtrOk_congr hhp hheap pf, numPtrOk_congr hhp hheap paf,
                numPtrOk_congr hhp hheap pab, numPtrOk_congr hhp hheap pcf,
                numPtrOk_congr hhp hheap pcb, ?_⟩
              rw [intVal_agree_heap hheap pcf.2.1 pcf.2.2.1,
                intVal_agree_heap hheap pcb.2.1 pcb.2.2.1, hcb_eq]
            · intro hhe0
              rw [heq_id OFF_HASE (by decide) (by decide) (by decide)] at hhe0
              rw [heq_id OFF_DIR (by decide) (by decide) (by decide),
                heq_id OFF_FLOW_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AF_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AB_PTR (by decide) (by decide) (by decide),
                heq_id OFF_COST_FWD (by decide) (by decide) (by decide),
                heq_id OFF_COST_BWD (by decide) (by decide) (by decide)]
              exact he0 hhe0
            · rw [heq_id OFF_CSUM_FWD (by decide) (by decide) (by decide)]
              exact optNumPtrOk_congr hhp hheap hcf
            · rw [heq_id OFF_CSUM_BWD (by decide) (by decide) (by decide)]
              exact optNumPtrOk_congr hhp hheap hcb
            · intro hht1
              rw [heq_id OFF_HAS_TAG (by decide) (by decide) (by decide)] at hht1
              rcases htag1 hht1 with ⟨pt, hch, d, hdmod, hfit⟩
              refine ⟨by rw [heq_id OFF_TAG_PTR (by decide) (by decide) (by decide)]; exact numPtrOk_congr hhp hheap pt, ?_, d, ?_, ?_⟩
              · rcases hch with hcl | hcr
                · left
                  rw [hl_m.min1Has_iff_evalSteps_ne_nil] at hcl
                  rw [hl_m2.min1Has_iff_evalSteps_ne_nil, hl_steps2]
                  exact hcl
                · right
                  rw [hr_m.min1Has_iff_evalSteps_ne_nil] at hcr
                  rw [hr_m2.min1Has_iff_evalSteps_ne_nil, hr_steps_fl]
                  exact hcr
              · rwa [htag_id]
              · rwa [hrev_id, hl_steps_fl, hr_steps_fl]
            · intro hht0
              rw [heq_id OFF_HAS_TAG (by decide) (by decide) (by decide)] at hht0
              rw [heq_id OFF_TAG_PTR (by decide) (by decide) (by decide),
                heq_id OFF_TAG_NEG (by decide) (by decide) (by decide)]
              exact htag0 hht0
            · simpa [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)] using hm1h
            · simpa [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_HAS (by decide) (by decide) (by decide)] using hm2h
            · intro hm11
              rw [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)] at hm11
              rcases hm1_1 hm11 with ⟨p1, p2, hf1, hl1, hf2, hl2⟩
              rw [heq_id OFF_MIN1_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_LAST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_LAST (by decide) (by decide) (by decide)]
              exact ⟨numPtrOk_congr hhp hheap p1, numPtrOk_congr hhp hheap p2, hf1, hl1, hf2, hl2⟩
            · intro hm10
              rw [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)] at hm10
              rw [heq_id OFF_MIN1_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_LAST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_LAST (by decide) (by decide) (by decide)]
              exact hm1_0 hm10
            · dsimp only
              rw [heval_node, hsteps_node]
              rcases hagg with ⟨hvc, hsf, hsb, hmiff, hm1, hm2⟩
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [heq_id OFF_VCNT (by decide) (by decide) (by decide), hvc, ← hvc_node, heval_node]
              · rw [heq_id OFF_CSUM_FWD (by decide) (by decide) (by decide),
                  optIntVal_agree_heap hheap hcf, hsf]
              · rw [heq_id OFF_CSUM_BWD (by decide) (by decide) (by decide),
                  optIntVal_agree_heap hheap hcb, hsb]
              · rw [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)]; exact hmiff
              · simp only [nodeIntMinAgg1,
                  heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide),
                  heq_id OFF_MIN1_VAL (by decide) (by decide) (by decide),
                  heq_id OFF_MIN1_FIRST (by decide) (by decide) (by decide),
                  heq_id OFF_MIN1_LAST (by decide) (by decide) (by decide)]
                have hval_eq : optIntVal mem₂ h L (nodeField mem₁ nodesBase id OFF_MIN1_VAL) =
                    optIntVal mem₁ h L (nodeField mem₁ nodesBase id OFF_MIN1_VAL) := by
                  by_cases hm11 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 1
                  · rcases hm1_1 hm11 with ⟨p1, _⟩
                    exact optIntVal_agree_heap hheap (Or.inr ⟨p1.2.1, p1.2.2.1, p1.2.2.2⟩)
                  · have hm10 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 0 := by omega
                    rw [(hm1_0 hm10).1]; simp [optIntVal]
                rw [hval_eq]; exact hm1
              · simp only [nodeIntMinAgg2,
                  heq_id OFF_MIN2_HAS (by decide) (by decide) (by decide),
                  heq_id OFF_MIN2_VAL (by decide) (by decide) (by decide),
                  heq_id OFF_MIN2_FIRST (by decide) (by decide) (by decide),
                  heq_id OFF_MIN2_LAST (by decide) (by decide) (by decide)]
                have hval_eq : optIntVal mem₂ h L (nodeField mem₁ nodesBase id OFF_MIN2_VAL) =
                    optIntVal mem₁ h L (nodeField mem₁ nodesBase id OFF_MIN2_VAL) := by
                  by_cases hm11 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 1
                  · rcases hm1_1 hm11 with ⟨_, p2, _⟩
                    exact optIntVal_agree_heap hheap (Or.inr ⟨p2.2.1, p2.2.2.1, p2.2.2.2⟩)
                  · have hm10 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 0 := by omega
                    rw [(hm1_0 hm10).2.2.2.1]; simp [optIntVal]
                rw [hval_eq]; exact hm2
          · rw [hrep_r]
            simpa [AuxTree.toList] using (hl_perm2.append_right [id]).append_right r.toList
        · have hnr : subId ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hsub
            rcases hsub with (hl | rfl) | hr_mem
            · exact absurd hl hnl
            · exact absurd rfl heq
            · exact hr_mem
          have hrep_l : l.replaceSubtree subId s' = l := AuxTree.replaceSubtree_not_mem hnl
          have hfind : (AuxTree.node id l r).findSubtree subId = r.findSubtree subId := by
            simp [AuxTree.findSubtree, heq, hnl]
          have hpar_r : (AuxTree.node id l r).parentIn subId p₀ = r.parentIn subId id := by
            simp [AuxTree.parentIn, heq, hnl]
          have hs_match_r : TreeMemMatch w h L mem₂ nodesBase cap s' (r.parentIn subId id)
              (if r.rootId = subId then 0 else 0) := by
            have h0 : (if r.rootId = subId then (0 : ℕ) else 0) = 0 := by split_ifs <;> rfl
            have hne_root : (AuxTree.node id l r).rootId ≠ subId := by simp [AuxTree.rootId, heq]
            simpa [hpar_r, hne_root, h0] using hs_match
          have hnot_in_l : ∀ u ∈ l.toList, u ∉ (r.findSubtree subId).toList := fun u hu hu_sub =>
            hdisj_lr u (Or.inl hu) u (AuxTree.findSubtree_subset hu_sub) rfl
          have hl_field_eq : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
              nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off := by
            intro u hu off hoff
            have hu_mem : u ∈ (AuxTree.node id l r).toList := by simp [AuxTree.toList, hu]
            have hu_nsub : u ∉ ((AuxTree.node id l r).findSubtree subId).toList := by
              rw [hfind]; exact hnot_in_l u hu
            by_cases hOL : off = OFF_LEFT
            · subst hOL
              rw [houter_left u hu_mem hu_nsub]
              have hc := TreeMemMatch.child_ne_of_not_mem hl_m hsub_pos hnl u hu
              simp [hc.1]
            · by_cases hOR : off = OFF_RIGHT
              · subst hOR
                rw [houter_right u hu_mem hu_nsub]
                have hc := TreeMemMatch.child_ne_of_not_mem hl_m hsub_pos hnl u hu
                simp [hc.2]
              · exact houter_other u hu_mem hu_nsub off hoff hOL hOR
          have hl_m2 : TreeMemMatch w h L mem₂ nodesBase cap l id 0 :=
            memAgree_treeMemMatch_of_nodeList hl_m hl_field_eq hhp hheap
          have hl_steps_fl : ∀ fl d,
              evalMemSteps mem₂ nodesBase h L l fl d = evalMemSteps mem₁ nodesBase h L l fl d :=
            fun fl d => evalMemSteps_agree hl_m hl_field_eq hheap fl d
          have houter_r_other : ∀ u ∈ r.toList, u ∉ (r.findSubtree subId).toList →
              ∀ off < NODE_STRIDE, off ≠ OFF_LEFT → off ≠ OFF_RIGHT →
                nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off :=
            fun u hu hn => houter_other u (by simp [AuxTree.toList, hu]) (by rwa [hfind])
          have houter_r_left : ∀ u ∈ r.toList, u ∉ (r.findSubtree subId).toList →
              nodeField mem₂ nodesBase u OFF_LEFT =
                if nodeField mem₁ nodesBase u OFF_LEFT = subId then s'.rootId
                else nodeField mem₁ nodesBase u OFF_LEFT :=
            fun u hu hn => houter_left u (by simp [AuxTree.toList, hu]) (by rwa [hfind])
          have houter_r_right : ∀ u ∈ r.toList, u ∉ (r.findSubtree subId).toList →
              nodeField mem₂ nodesBase u OFF_RIGHT =
                if nodeField mem₁ nodesBase u OFF_RIGHT = subId then s'.rootId
                else nodeField mem₁ nodesBase u OFF_RIGHT :=
            fun u hu hn => houter_right u (by simp [AuxTree.toList, hu]) (by rwa [hfind])
          rcases ihr hr_m hr_nd hnr hs_match_r (by simpa [hfind] using hs_perm)
              (by simpa [hfind] using hs_eval) (by simpa [hfind] using hs_vcnt)
              (by simpa [hfind] using hs_steps)
              houter_r_other houter_r_left houter_r_right with
            ⟨hr_m2, hr_perm2, hr_eval2, hr_vcnt2, hr_steps2⟩
          have hr_eval_true : (r.replaceSubtree subId s').evalInorder (revFlag mem₂ nodesBase) true =
              r.evalInorder (revFlag mem₁ nodesBase) true := by
            rw [AuxTree.evalInorder_true, hr_eval2, AuxTree.evalInorder_true]
          have hl_eval_any : ∀ b, l.evalInorder (revFlag mem₂ nodesBase) b =
              l.evalInorder (revFlag mem₁ nodesBase) b :=
            fun b => AuxTree.evalInorder_agree _ _ l b fun u hu => by
              simp [revFlag, hl_field_eq u hu OFF_REV (by decide)]
          have heval_node : (AuxTree.node id l (r.replaceSubtree subId s')).evalInorder (revFlag mem₂ nodesBase) false =
              (AuxTree.node id l r).evalInorder (revFlag mem₁ nodesBase) false := by
            cases hrv : revFlag mem₁ nodesBase id <;>
              simp [AuxTree.evalInorder, hrev_id, hrv, hr_eval2, hr_eval_true, hl_eval_any]
          have hr_steps_fl := heval_steps_branch r hr_steps2 hr_m2 hr_m
          have hsteps_node : evalMemSteps mem₂ nodesBase h L (AuxTree.node id l (r.replaceSubtree subId s')) false 0 =
              evalMemSteps mem₁ nodesBase h L (AuxTree.node id l r) false 0 := by
            simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor,
              hown_id, htag_id, hrev_id, hl_steps_fl, hr_steps_fl]
          have hvc_node : listVcnt mem₂ nodesBase ((AuxTree.node id l (r.replaceSubtree subId s')).evalInorder (revFlag mem₂ nodesBase) false) =
              listVcnt mem₁ nodesBase ((AuxTree.node id l r).evalInorder (revFlag mem₁ nodesBase) false) := by
            have hr_vc_rev : listVcnt mem₂ nodesBase (r.evalInorder (revFlag mem₁ nodesBase) true) =
                listVcnt mem₁ nodesBase (r.evalInorder (revFlag mem₁ nodesBase) true) := by
              rw [AuxTree.evalInorder_true, listVcnt_reverse, listVcnt_reverse]
              rw [hr_eval2] at hr_vcnt2; exact hr_vcnt2
            have hl_vc : ∀ b, listVcnt mem₂ nodesBase (l.evalInorder (revFlag mem₁ nodesBase) b) =
                listVcnt mem₁ nodesBase (l.evalInorder (revFlag mem₁ nodesBase) b) := fun b => by
              apply listVcnt_agree_of_mem
              intro u hu
              have hu_l := (l.evalInorder_perm (revFlag mem₁ nodesBase) b).mem_iff.mp hu
              exact hl_field_eq u hu_l OFF_ISV (by decide)
            rw [heval_node]
            cases hrv : revFlag mem₁ nodesBase id <;>
              simp only [AuxTree.evalInorder, hrv, listVcnt_append, listVcnt,
                heq_id OFF_ISV (by decide) (by decide) (by decide)]
            · rw [hr_eval2] at hr_vcnt2; rw [hr_vcnt2, hl_vc false]
            · rw [hl_vc true, hr_vc_rev]
          have hroot_r : (r.replaceSubtree subId s').rootId =
              if r.rootId = subId then s'.rootId else r.rootId :=
            AuxTree.replaceSubtree_rootId
              (by cases r with | leaf => simp [AuxTree.toList] at hnr | node _ _ _ => simp)
              hs_ne
          have hR' : nodeField mem₂ nodesBase id OFF_RIGHT = (r.replaceSubtree subId s').rootId := by
            rw [houter_right id hid_mem hnot_sub_id, hR, hroot_r]
          have hL' : nodeField mem₂ nodesBase id OFF_LEFT = l.rootId := by
            rw [houter_left id hid_mem hnot_sub_id, hL]
            cases l with
            | leaf =>
                have : (0 : ℕ) ≠ subId := by omega
                simp [AuxTree.rootId, this]
            | node lid _ _ =>
                have : lid ≠ subId := fun he => hnl (he ▸ by simp [AuxTree.toList])
                simp [AuxTree.rootId, this]
          refine ⟨?_, ?_, by rw [hrep_l]; exact heval_node, by rw [hrep_l]; exact hvc_node,
            by rw [hrep_l]; exact hsteps_node⟩
          · rw [hrep_l]
            refine ⟨hx1, hx2, hL', hR', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hl_m2, hr_m2⟩
            · simpa [heq_id OFF_PARENT (by decide) (by decide) (by decide)] using hP
            · simpa [heq_id OFF_PPAR (by decide) (by decide) (by decide)] using hPP
            · simpa [heq_id OFF_REV (by decide) (by decide) (by decide)] using hr
            · simpa [heq_id OFF_ISV (by decide) (by decide) (by decide)] using hiv
            · simpa [heq_id OFF_HASE (by decide) (by decide) (by decide)] using hhe
            · simpa [heq_id OFF_ISV (by decide) (by decide) (by decide),
                heq_id OFF_HASE (by decide) (by decide) (by decide)] using hsum
            · simpa [heq_id OFF_DIR (by decide) (by decide) (by decide)] using hdir
            · simpa [heq_id OFF_HAS_TAG (by decide) (by decide) (by decide)] using hht
            · simpa [heq_id OFF_TAG_NEG (by decide) (by decide) (by decide)] using htn
            · simpa [heq_id OFF_EU (by decide) (by decide) (by decide)] using heu
            · simpa [heq_id OFF_EV (by decide) (by decide) (by decide)] using hev
            · simpa [heq_id OFF_EID (by decide) (by decide) (by decide)] using heid
            · intro hhe1
              rw [heq_id OFF_HASE (by decide) (by decide) (by decide)] at hhe1
              rcases he1 hhe1 with ⟨pf, paf, pab, pcf, pcb, hcb_eq⟩
              rw [heq_id OFF_FLOW_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AF_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AB_PTR (by decide) (by decide) (by decide),
                heq_id OFF_COST_FWD (by decide) (by decide) (by decide),
                heq_id OFF_COST_BWD (by decide) (by decide) (by decide)]
              refine ⟨numPtrOk_congr hhp hheap pf, numPtrOk_congr hhp hheap paf,
                numPtrOk_congr hhp hheap pab, numPtrOk_congr hhp hheap pcf,
                numPtrOk_congr hhp hheap pcb, ?_⟩
              rw [intVal_agree_heap hheap pcf.2.1 pcf.2.2.1,
                intVal_agree_heap hheap pcb.2.1 pcb.2.2.1, hcb_eq]
            · intro hhe0
              rw [heq_id OFF_HASE (by decide) (by decide) (by decide)] at hhe0
              rw [heq_id OFF_DIR (by decide) (by decide) (by decide),
                heq_id OFF_FLOW_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AF_PTR (by decide) (by decide) (by decide),
                heq_id OFF_AB_PTR (by decide) (by decide) (by decide),
                heq_id OFF_COST_FWD (by decide) (by decide) (by decide),
                heq_id OFF_COST_BWD (by decide) (by decide) (by decide)]
              exact he0 hhe0
            · rw [heq_id OFF_CSUM_FWD (by decide) (by decide) (by decide)]
              exact optNumPtrOk_congr hhp hheap hcf
            · rw [heq_id OFF_CSUM_BWD (by decide) (by decide) (by decide)]
              exact optNumPtrOk_congr hhp hheap hcb
            · intro hht1
              rw [heq_id OFF_HAS_TAG (by decide) (by decide) (by decide)] at hht1
              rcases htag1 hht1 with ⟨pt, hch, d, hdmod, hfit⟩
              refine ⟨by rw [heq_id OFF_TAG_PTR (by decide) (by decide) (by decide)]; exact numPtrOk_congr hhp hheap pt, ?_, d, ?_, ?_⟩
              · rcases hch with hcl | hcr
                · left
                  rw [hl_m.min1Has_iff_evalSteps_ne_nil] at hcl
                  rw [hl_m2.min1Has_iff_evalSteps_ne_nil, hl_steps_fl]
                  exact hcl
                · right
                  rw [hr_m.min1Has_iff_evalSteps_ne_nil] at hcr
                  rw [hr_m2.min1Has_iff_evalSteps_ne_nil, hr_steps2]
                  exact hcr
              · rwa [htag_id]
              · rwa [hrev_id, hl_steps_fl, hr_steps_fl]
            · intro hht0
              rw [heq_id OFF_HAS_TAG (by decide) (by decide) (by decide)] at hht0
              rw [heq_id OFF_TAG_PTR (by decide) (by decide) (by decide),
                heq_id OFF_TAG_NEG (by decide) (by decide) (by decide)]
              exact htag0 hht0
            · simpa [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)] using hm1h
            · simpa [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_HAS (by decide) (by decide) (by decide)] using hm2h
            · intro hm11
              rw [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)] at hm11
              rcases hm1_1 hm11 with ⟨p1, p2, hf1, hl1, hf2, hl2⟩
              rw [heq_id OFF_MIN1_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_LAST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_LAST (by decide) (by decide) (by decide)]
              exact ⟨numPtrOk_congr hhp hheap p1, numPtrOk_congr hhp hheap p2, hf1, hl1, hf2, hl2⟩
            · intro hm10
              rw [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)] at hm10
              rw [heq_id OFF_MIN1_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN1_LAST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_VAL (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_FIRST (by decide) (by decide) (by decide),
                heq_id OFF_MIN2_LAST (by decide) (by decide) (by decide)]
              exact hm1_0 hm10
            · dsimp only
              rw [heval_node, hsteps_node]
              rcases hagg with ⟨hvc, hsf, hsb, hmiff, hm1, hm2⟩
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [heq_id OFF_VCNT (by decide) (by decide) (by decide), hvc, ← hvc_node, heval_node]
              · rw [heq_id OFF_CSUM_FWD (by decide) (by decide) (by decide),
                  optIntVal_agree_heap hheap hcf, hsf]
              · rw [heq_id OFF_CSUM_BWD (by decide) (by decide) (by decide),
                  optIntVal_agree_heap hheap hcb, hsb]
              · rw [heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide)]; exact hmiff
              · simp only [nodeIntMinAgg1,
                  heq_id OFF_MIN1_HAS (by decide) (by decide) (by decide),
                  heq_id OFF_MIN1_VAL (by decide) (by decide) (by decide),
                  heq_id OFF_MIN1_FIRST (by decide) (by decide) (by decide),
                  heq_id OFF_MIN1_LAST (by decide) (by decide) (by decide)]
                have hval_eq : optIntVal mem₂ h L (nodeField mem₁ nodesBase id OFF_MIN1_VAL) =
                    optIntVal mem₁ h L (nodeField mem₁ nodesBase id OFF_MIN1_VAL) := by
                  by_cases hm11 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 1
                  · rcases hm1_1 hm11 with ⟨p1, _⟩
                    exact optIntVal_agree_heap hheap (Or.inr ⟨p1.2.1, p1.2.2.1, p1.2.2.2⟩)
                  · have hm10 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 0 := by omega
                    rw [(hm1_0 hm10).1]; simp [optIntVal]
                rw [hval_eq]; exact hm1
              · simp only [nodeIntMinAgg2,
                  heq_id OFF_MIN2_HAS (by decide) (by decide) (by decide),
                  heq_id OFF_MIN2_VAL (by decide) (by decide) (by decide),
                  heq_id OFF_MIN2_FIRST (by decide) (by decide) (by decide),
                  heq_id OFF_MIN2_LAST (by decide) (by decide) (by decide)]
                have hval_eq : optIntVal mem₂ h L (nodeField mem₁ nodesBase id OFF_MIN2_VAL) =
                    optIntVal mem₁ h L (nodeField mem₁ nodesBase id OFF_MIN2_VAL) := by
                  by_cases hm11 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 1
                  · rcases hm1_1 hm11 with ⟨_, p2, _⟩
                    exact optIntVal_agree_heap hheap (Or.inr ⟨p2.2.1, p2.2.2.1, p2.2.2.2⟩)
                  · have hm10 : nodeField mem₁ nodesBase id OFF_MIN1_HAS = 0 := by omega
                    rw [(hm1_0 hm10).2.2.2.1]; simp [optIntVal]
                rw [hval_eq]; exact hm2
          · rw [hrep_l]
            simpa [AuxTree.toList, List.append_assoc] using
              (hr_perm2.append_left [id]).append_left l.toList

end AuxTreeSurgery
end MinCostFlow.LinkCut.Prog
