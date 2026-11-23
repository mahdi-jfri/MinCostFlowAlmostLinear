module

public import MinCostFlow.LinkCut.Prog.SplayRotateProps
public import MinCostFlow.LinkCut.Prog.SplayStepPull

/-!
Memory/statement building blocks for `rotateBody`:
- Address separation helpers (`node_field_addr_ne`, `node_same_field_addr_ne`, `node_field_addr_outside`).
- Child/parent correspondence (`treeMemMatch_child_mem_or_zero`, `treeMemMatch_child_field_eq_parentIn`).
- Root reparenting for L-limb `Num` `TreeMemMatch` (`treeMemMatch_reparent_root`).
- Node `PullPre` extraction from `IsNonStructNonAggOff` agreement (`pullPre_of_nonStruct_agree`).
- `setChildAndParentStmt_runs`, `rotateBody_zero_runs`, `rotatePrefix_exec`.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

@[expose] public section

theorem node_field_addr_ne {nodesBase u v off1 off2 : ℕ}
    (huv : u ≠ v) (ho1 : off1 < NODE_STRIDE) (ho2 : off2 < NODE_STRIDE) :
    nodesBase + NODE_STRIDE * u + off1 ≠ nodesBase + NODE_STRIDE * v + off2 := by
  unfold NODE_STRIDE at ho1 ho2 ⊢
  rcases lt_or_gt_of_ne huv with h | h <;> omega

theorem node_same_field_addr_ne {nodesBase u off1 off2 : ℕ} (hne : off1 ≠ off2) :
    nodesBase + NODE_STRIDE * u + off1 ≠ nodesBase + NODE_STRIDE * u + off2 :=
  fun h => hne (Nat.add_left_cancel h)

theorem node_field_addr_outside {nodesBase u p off : ℕ}
    (hup : u ≠ p) (hoff : off < NODE_STRIDE) :
    nodesBase + NODE_STRIDE * u + off < nodesBase + NODE_STRIDE * p ∨
    nodesBase + NODE_STRIDE * p + NODE_STRIDE ≤ nodesBase + NODE_STRIDE * u + off := by
  unfold NODE_STRIDE at hoff ⊢
  rcases lt_or_gt_of_ne hup with h | h <;> [left; right] <;> omega

theorem treeMemMatch_child_mem_or_zero {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {q : AuxTree} {qp qpp u : ℕ}
    (hq : TreeMemMatch w h L mem nodesBase cap q qp qpp) (hu : u ∈ q.toList) :
    (nodeField mem nodesBase u OFF_LEFT = 0 ∨ nodeField mem nodesBase u OFF_LEFT ∈ q.toList) ∧
    (nodeField mem nodesBase u OFF_RIGHT = 0 ∨ nodeField mem nodesBase u OFF_RIGHT ∈ q.toList) := by
  induction q generalizing qp qpp with
  | leaf => simp [AuxTree.toList] at hu
  | node id l r ihl ihr =>
      rcases hq with ⟨_, _, hL, hR, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hlm | rfl) | hrm
      · rcases ihl hl hlm with ⟨hl1, hl2⟩
        exact ⟨hl1.imp _root_.id (fun h => by simp [AuxTree.toList, h]),
          hl2.imp _root_.id (fun h => by simp [AuxTree.toList, h])⟩
      · constructor
        · cases l with
          | leaf => exact Or.inl (by simpa [AuxTree.rootId] using hL)
          | node lid _ _ => exact Or.inr (by rw [hL]; simp [AuxTree.rootId, AuxTree.toList])
        · cases r with
          | leaf => exact Or.inl (by simpa [AuxTree.rootId] using hR)
          | node rid _ _ => exact Or.inr (by rw [hR]; simp [AuxTree.rootId, AuxTree.toList])
      · rcases ihr hr hrm with ⟨hr1, hr2⟩
        exact ⟨hr1.imp _root_.id (fun h => by simp [AuxTree.toList, h]),
          hr2.imp _root_.id (fun h => by simp [AuxTree.toList, h])⟩

theorem treeMemMatch_child_field_eq_parentIn {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p₀ pp₀ subId u : ℕ}
    (ht : TreeMemMatch w h L mem nodesBase cap t p₀ pp₀)
    (hnd : t.toList.Nodup) (hsub : subId ∈ t.toList) (hu : u ∈ t.toList) :
    (nodeField mem nodesBase u OFF_LEFT = subId →
      u = t.parentIn subId p₀ ∧ nodeField mem nodesBase u OFF_RIGHT ≠ subId) ∧
    (nodeField mem nodesBase u OFF_RIGHT = subId →
      u = t.parentIn subId p₀ ∧ nodeField mem nodesBase u OFF_LEFT ≠ subId) := by
  have hsub_pos : 1 ≤ subId := (ht.nodup_perm_mem hsub).1
  induction t generalizing p₀ pp₀ with
  | leaf => simp [AuxTree.toList] at hsub
  | node id l r ihl ihr =>
      rcases ht with ⟨_, _, hL, hR, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      have hnd' := hnd
      simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, hdisj_id_l⟩, hr_nd, hdisj_lr⟩
      have hid_nin_l : id ∉ l.toList := fun h => hdisj_id_l id h id rfl rfl
      have hid_nin_r : id ∉ r.toList := fun h => hdisj_lr id (Or.inr rfl) id h rfl
      have hdisj_lr' : ∀ a ∈ l.toList, a ∉ r.toList := fun a ha hrm => hdisj_lr a (Or.inl ha) a hrm rfl
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hul | rfl) | hur
      · have hL_sub := (treeMemMatch_child_mem_or_zero hl hul).1
        have hR_sub := (treeMemMatch_child_mem_or_zero hl hul).2
        constructor
        · intro h
          have hsub_l : subId ∈ l.toList := by
            rcases hL_sub with h0 | hm
            · omega
            · rwa [h] at hm
          have hne_id : id ≠ subId := fun he => hid_nin_l (he ▸ hsub_l)
          rcases (ihl hl hl_nd hsub_l hul).1 h with ⟨hu_eq, hR_ne⟩
          exact ⟨by simpa [AuxTree.parentIn, hne_id, hsub_l] using hu_eq, hR_ne⟩
        · intro h
          have hsub_l : subId ∈ l.toList := by
            rcases hR_sub with h0 | hm
            · omega
            · rwa [h] at hm
          have hne_id : id ≠ subId := fun he => hid_nin_l (he ▸ hsub_l)
          rcases (ihl hl hl_nd hsub_l hul).2 h with ⟨hu_eq, hL_ne⟩
          exact ⟨by simpa [AuxTree.parentIn, hne_id, hsub_l] using hu_eq, hL_ne⟩
      · constructor
        · intro h
          rw [hL] at h
          cases l with
          | leaf => simp [AuxTree.rootId] at h; omega
          | node lid _ _ =>
              simp only [AuxTree.rootId] at h
              subst h
              have hne_id : u ≠ lid := fun he => hid_nin_l (he ▸ by simp [AuxTree.toList])
              have hnin_r : lid ∉ r.toList := hdisj_lr' lid (by simp [AuxTree.toList])
              have hR_ne : nodeField mem nodesBase u OFF_RIGHT ≠ lid := by
                rw [hR]
                cases r with
                | leaf => simp [AuxTree.rootId]; omega
                | node rid _ _ =>
                    simp only [AuxTree.rootId]; intro he; subst he; exact hnin_r (by simp [AuxTree.toList])
              exact ⟨by simp [AuxTree.parentIn, hne_id, AuxTree.toList], hR_ne⟩
        · intro h
          rw [hR] at h
          cases r with
          | leaf => simp [AuxTree.rootId] at h; omega
          | node rid _ _ =>
              simp only [AuxTree.rootId] at h
              subst h
              have hne_id : u ≠ rid := fun he => hid_nin_r (he ▸ by simp [AuxTree.toList])
              have hnin_l : rid ∉ l.toList := fun hm => hdisj_lr' rid hm (by simp [AuxTree.toList])
              have hL_ne : nodeField mem nodesBase u OFF_LEFT ≠ rid := by
                rw [hL]
                cases l with
                | leaf => simp [AuxTree.rootId]; omega
                | node lid _ _ =>
                    simp only [AuxTree.rootId]; intro he; subst he; exact hnin_l (by simp [AuxTree.toList])
              exact ⟨by simp [AuxTree.parentIn, hne_id, hnin_l], hL_ne⟩
      · have hL_sub := (treeMemMatch_child_mem_or_zero hr hur).1
        have hR_sub := (treeMemMatch_child_mem_or_zero hr hur).2
        constructor
        · intro h
          have hsub_r : subId ∈ r.toList := by
            rcases hL_sub with h0 | hm
            · omega
            · rwa [h] at hm
          have hne_id : id ≠ subId := fun he => hid_nin_r (he ▸ hsub_r)
          have hnin_l : subId ∉ l.toList := fun hm => hdisj_lr' subId hm hsub_r
          rcases (ihr hr hr_nd hsub_r hur).1 h with ⟨hu_eq, hR_ne⟩
          exact ⟨by simpa [AuxTree.parentIn, hne_id, hnin_l] using hu_eq, hR_ne⟩
        · intro h
          have hsub_r : subId ∈ r.toList := by
            rcases hR_sub with h0 | hm
            · omega
            · rwa [h] at hm
          have hne_id : id ≠ subId := fun he => hid_nin_r (he ▸ hsub_r)
          have hnin_l : subId ∉ l.toList := fun hm => hdisj_lr' subId hm hsub_r
          rcases (ihr hr hr_nd hsub_r hur).2 h with ⟨hu_eq, hL_ne⟩
          exact ⟨by simpa [AuxTree.parentIn, hne_id, hnin_l] using hu_eq, hL_ne⟩

theorem treeMemMatch_reparent_root {w h L : ℕ} {mem₀ mem₁ : ℕ → ℕ} {nodesBase cap : ℕ}
    {s : AuxTree} {oldP oldPP newP newPP : ℕ}
    (hs : TreeMemMatch w h L mem₀ nodesBase cap s oldP oldPP)
    (hnd : s.toList.Nodup)
    (hpar : s ≠ .leaf → nodeField mem₁ nodesBase s.rootId OFF_PARENT = newP)
    (hpp : s ≠ .leaf → nodeField mem₁ nodesBase s.rootId OFF_PPAR = newPP)
    (hother : ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
      (u = s.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off)
    (hle : mem₀ (nodesBase - 1) ≤ mem₁ (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
      mem₁ a = mem₀ a) :
    TreeMemMatch w h L mem₁ nodesBase cap s newP newPP := by
  cases s with
  | leaf => trivial
  | node r0 l r =>
      have hs_ok : ∀ u ∈ (AuxTree.node r0 l r).toList,
          NodeNonStructOk h L (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) nodesBase mem₀ u :=
        fun u hu => hs.nodeNonStructOk hu
      rcases hs with ⟨hx1, hx2, hL, hR, _, _, hrev, hiv, hhe, hsum, hdir, hht, htn, heu, hev, heid,
        he1, he0, hcf, hcb, ht1, ht0, hm1h, hm2h, hm1nz, hm1z, hagg, hl, hr'⟩
      have hnd' := hnd
      simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨_, _, hdisj_r_l⟩, _, hdisj_lr⟩
      have hr0_nin_l : r0 ∉ l.toList := fun h => hdisj_r_l r0 h r0 rfl rfl
      have hr0_nin_r : r0 ∉ r.toList := fun h => hdisj_lr r0 (Or.inr rfl) r0 h rfl
      have hr0_other : ∀ off < NODE_STRIDE, off ≠ OFF_PARENT → off ≠ OFF_PPAR →
          nodeField mem₁ nodesBase r0 off = nodeField mem₀ nodesBase r0 off :=
        fun off hoff hp1 hp2 => hother r0 (by simp [AuxTree.toList]) off hoff (fun _ => ⟨hp1, hp2⟩)
      have hl_agree : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu off hoff =>
        hother u (by simp [AuxTree.toList, hu]) off hoff fun h => by
          simp only [AuxTree.rootId] at h; subst h; exact absurd hu hr0_nin_l
      have hr_agree : ∀ u ∈ r.toList, ∀ off < NODE_STRIDE,
          nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu off hoff =>
        hother u (by simp [AuxTree.toList, hu]) off hoff fun h => by
          simp only [AuxTree.rootId] at h; subst h; exact absurd hu hr0_nin_r
      have hs_agree : ∀ u ∈ (AuxTree.node r0 l r).toList,
          revFlag mem₁ nodesBase u = revFlag mem₀ nodesBase u := fun u hu => by
        simp only [revFlag]
        rw [hother u hu OFF_REV (by decide) (fun _ => ⟨by decide, by decide⟩)]
      have heval : (AuxTree.node r0 l r).evalInorder (revFlag mem₁ nodesBase) false =
          (AuxTree.node r0 l r).evalInorder (revFlag mem₀ nodesBase) false :=
        AuxTree.evalInorder_agree _ _ _ false hs_agree
      have hnode_ns : ∀ u ∈ (AuxTree.node r0 l r).toList, ∀ off, IsNonStructNonAggOff off →
          nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off := by
        intro u hu off hoff
        exact hother u hu off hoff.1 (fun _ => ⟨hoff.2.2.2.1, hoff.2.2.2.2.1⟩)
      have hsteps : evalMemSteps mem₁ nodesBase h L (AuxTree.node r0 l r) false 0 =
          evalMemSteps mem₀ nodesBase h L (AuxTree.node r0 l r) false 0 :=
        evalMemSteps_agree_nonStruct hs_ok hnode_ns hheap false 0
      have hseq_sub : ∀ u ∈ (AuxTree.node r0 l r).evalInorder (revFlag mem₀ nodesBase) false,
          u ∈ (AuxTree.node r0 l r).toList := fun u hu =>
        ((AuxTree.node r0 l r).evalInorder_perm (revFlag mem₀ nodesBase) false).mem_iff.1 hu
      refine ⟨hx1, hx2,
        by rw [hr0_other OFF_LEFT (by decide) (by decide) (by decide)]; exact hL,
        by rw [hr0_other OFF_RIGHT (by decide) (by decide) (by decide)]; exact hR,
        hpar (by simp), hpp (by simp),
        by rw [hr0_other OFF_REV (by decide) (by decide) (by decide)]; exact hrev,
        by rw [hr0_other OFF_ISV (by decide) (by decide) (by decide)]; exact hiv,
        by rw [hr0_other OFF_HASE (by decide) (by decide) (by decide)]; exact hhe,
        by rw [hr0_other OFF_ISV (by decide) (by decide) (by decide),
               hr0_other OFF_HASE (by decide) (by decide) (by decide)]; exact hsum,
        by rw [hr0_other OFF_DIR (by decide) (by decide) (by decide)]; exact hdir,
        by rw [hr0_other OFF_HAS_TAG (by decide) (by decide) (by decide)]; exact hht,
        by rw [hr0_other OFF_TAG_NEG (by decide) (by decide) (by decide)]; exact htn,
        by rw [hr0_other OFF_EU (by decide) (by decide) (by decide)]; exact heu,
        by rw [hr0_other OFF_EV (by decide) (by decide) (by decide)]; exact hev,
        by rw [hr0_other OFF_EID (by decide) (by decide) (by decide)]; exact heid,
        ?_, ?_,
        by rw [hr0_other OFF_CSUM_FWD (by decide) (by decide) (by decide)]
           exact optNumPtrOk_congr hle hheap hcf,
        by rw [hr0_other OFF_CSUM_BWD (by decide) (by decide) (by decide)]
           exact optNumPtrOk_congr hle hheap hcb,
        ?_, ?_,
        by rw [hr0_other OFF_MIN1_HAS (by decide) (by decide) (by decide)]; exact hm1h,
        by rw [hr0_other OFF_MIN2_HAS (by decide) (by decide) (by decide),
               hr0_other OFF_MIN1_HAS (by decide) (by decide) (by decide)]; exact hm2h,
        ?_, ?_, ?_,
        memAgree_treeMemMatch_of_nodeList hl hl_agree hle hheap,
        memAgree_treeMemMatch_of_nodeList hr' hr_agree hle hheap⟩
      · rw [hr0_other OFF_HASE (by decide) (by decide) (by decide),
            hr0_other OFF_FLOW_PTR (by decide) (by decide) (by decide),
            hr0_other OFF_AF_PTR (by decide) (by decide) (by decide),
            hr0_other OFF_AB_PTR (by decide) (by decide) (by decide),
            hr0_other OFF_COST_FWD (by decide) (by decide) (by decide),
            hr0_other OFF_COST_BWD (by decide) (by decide) (by decide)]
        intro h1
        obtain ⟨kfl, kaf, kab, kcf, kcb, hcw⟩ := he1 h1
        refine ⟨numPtrOk_congr hle hheap kfl, numPtrOk_congr hle hheap kaf,
          numPtrOk_congr hle hheap kab, numPtrOk_congr hle hheap kcf,
          numPtrOk_congr hle hheap kcb, ?_⟩
        rw [intVal_agree_heap hheap kcb.2.1 kcb.2.2.1, intVal_agree_heap hheap kcf.2.1 kcf.2.2.1]
        exact hcw
      · rw [hr0_other OFF_HASE (by decide) (by decide) (by decide),
            hr0_other OFF_DIR (by decide) (by decide) (by decide),
            hr0_other OFF_FLOW_PTR (by decide) (by decide) (by decide),
            hr0_other OFF_AF_PTR (by decide) (by decide) (by decide),
            hr0_other OFF_AB_PTR (by decide) (by decide) (by decide),
            hr0_other OFF_COST_FWD (by decide) (by decide) (by decide),
            hr0_other OFF_COST_BWD (by decide) (by decide) (by decide)]
        exact he0
      · rw [hr0_other OFF_HAS_TAG (by decide) (by decide) (by decide),
            hr0_other OFF_TAG_PTR (by decide) (by decide) (by decide)]
        intro h1
        obtain ⟨ktp, hne_ch, d, hd_eq, hfit⟩ := ht1 h1
        refine ⟨numPtrOk_congr hle hheap ktp, ?_, d, ?_, ?_⟩
        · rcases hne_ch with ⟨hl_nl, hl_m⟩ | ⟨hr_nl, hr_m⟩
          · refine Or.inl ⟨hl_nl, ?_⟩
            have hl_rmem : l.rootId ∈ l.toList := by
              cases l with
              | leaf => exact absurd rfl hl_nl
              | node lid _ _ => simp [AuxTree.rootId, AuxTree.toList]
            rw [hl_agree l.rootId hl_rmem OFF_MIN1_HAS (by decide)]; exact hl_m
          · refine Or.inr ⟨hr_nl, ?_⟩
            have hr_rmem : r.rootId ∈ r.toList := by
              cases r with
              | leaf => exact absurd rfl hr_nl
              | node rid _ _ => simp [AuxTree.rootId, AuxTree.toList]
            rw [hr_agree r.rootId hr_rmem OFF_MIN1_HAS (by decide)]; exact hr_m
        · have htag_eq : nodeTagInt mem₁ nodesBase h L r0 = nodeTagInt mem₀ nodesBase h L r0 :=
            nodeTagInt_agree_nonStruct (hs_ok r0 (by simp [AuxTree.toList]))
              (hnode_ns r0 (by simp [AuxTree.toList])) hheap
          rw [htag_eq]; exact hd_eq
        · have hrev_r0 : revFlag mem₁ nodesBase r0 = revFlag mem₀ nodesBase r0 := by
            simp [revFlag, hr0_other OFF_REV (by decide) (by decide) (by decide)]
          rw [hrev_r0, evalMemSteps_agree hl hl_agree hheap, evalMemSteps_agree hr' hr_agree hheap]
          exact hfit
      · rw [hr0_other OFF_HAS_TAG (by decide) (by decide) (by decide),
            hr0_other OFF_TAG_PTR (by decide) (by decide) (by decide),
            hr0_other OFF_TAG_NEG (by decide) (by decide) (by decide)]
        exact ht0
      · rw [hr0_other OFF_MIN1_HAS (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_VAL (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_VAL (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_FIRST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_LAST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_FIRST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_LAST (by decide) (by decide) (by decide)]
        intro h1
        obtain ⟨k1, k2, h1f, h1l, h2f, h2l⟩ := hm1nz h1
        exact ⟨numPtrOk_congr hle hheap k1, numPtrOk_congr hle hheap k2, h1f, h1l, h2f, h2l⟩
      · rw [hr0_other OFF_MIN1_HAS (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_VAL (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_FIRST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_LAST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_VAL (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_FIRST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_LAST (by decide) (by decide) (by decide)]
        exact hm1z
      · rcases hagg with ⟨hvc, hscf, hscb, hsh, hm1, hm2⟩
        have hvc_eq : listVcnt mem₁ nodesBase ((AuxTree.node r0 l r).evalInorder (revFlag mem₀ nodesBase) false) =
            listVcnt mem₀ nodesBase ((AuxTree.node r0 l r).evalInorder (revFlag mem₀ nodesBase) false) :=
          listVcnt_agree_of_mem fun u hu =>
            hother u (hseq_sub u hu) OFF_ISV (by decide) (fun _ => ⟨by decide, by decide⟩)
        refine ⟨by rw [heval, hvc_eq, hr0_other OFF_VCNT (by decide) (by decide) (by decide), hvc],
          ?_, ?_, ?_, ?_, ?_⟩
        · rw [hsteps, hr0_other OFF_CSUM_FWD (by decide) (by decide) (by decide),
              optIntVal_agree_heap hheap hcf, hscf]
        · rw [hsteps, hr0_other OFF_CSUM_BWD (by decide) (by decide) (by decide),
              optIntVal_agree_heap hheap hcb, hscb]
        · rw [hsteps, hr0_other OFF_MIN1_HAS (by decide) (by decide) (by decide)]; exact hsh
        · have hm1v_ok : OptNumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1))
              h L (nodeField mem₀ nodesBase r0 OFF_MIN1_VAL) := by
            by_cases h0 : nodeField mem₀ nodesBase r0 OFF_MIN1_HAS = 0
            · exact Or.inl (hm1z h0).1
            · exact Or.inr (hm1nz (eq_one_of_le_one_ne_zero hm1h h0)).1.2
          rw [hsteps, ← hm1]
          simp [nodeIntMinAgg1, hr0_other OFF_MIN1_HAS (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_VAL (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_FIRST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN1_LAST (by decide) (by decide) (by decide),
            optIntVal_agree_heap hheap hm1v_ok]
        · have hm2v_ok : OptNumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1))
              h L (nodeField mem₀ nodesBase r0 OFF_MIN2_VAL) := by
            by_cases h0 : nodeField mem₀ nodesBase r0 OFF_MIN1_HAS = 0
            · exact Or.inl (hm1z h0).2.2.2.1
            · exact Or.inr (hm1nz (eq_one_of_le_one_ne_zero hm1h h0)).2.1.2
          rw [hsteps, ← hm2]
          simp [nodeIntMinAgg2, hr0_other OFF_MIN2_HAS (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_VAL (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_FIRST (by decide) (by decide) (by decide),
            hr0_other OFF_MIN2_LAST (by decide) (by decide) (by decide),
            optIntVal_agree_heap hheap hm2v_ok]

private theorem listVcnt_le_length {mem : ℕ → ℕ} {nodesBase : ℕ} {seq : List ℕ}
    (hiv : ∀ u ∈ seq, nodeField mem nodesBase u OFF_ISV ≤ 1) :
    listVcnt mem nodesBase seq ≤ seq.length := by
  induction seq with
  | nil => simp [listVcnt]
  | cons u us ih =>
      have h1 := hiv u (by simp)
      have h2 := ih (fun v hv => hiv v (by simp [hv]))
      simp [listVcnt]; omega

theorem listVcnt_lt_pow_of_le {w cap : ℕ} {mem : ℕ → ℕ} {nodesBase : ℕ} {seq : List ℕ}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnd : seq.Nodup) (hb : ∀ u ∈ seq, 1 ≤ u ∧ u ≤ cap)
    (hiv : ∀ u ∈ seq, nodeField mem nodesBase u OFF_ISV ≤ 1) :
    listVcnt mem nodesBase seq < 2 ^ w := by
  have hsub : seq.toFinset ⊆ ((List.range cap).map (· + 1)).toFinset := by
    intro u hu
    rw [List.mem_toFinset] at hu ⊢
    rcases hb u hu with ⟨hu1, hu2⟩
    exact List.mem_map.mpr ⟨u - 1, List.mem_range.mpr (by omega), by omega⟩
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at hc
  have hc2 : ((List.range cap).map (· + 1)).toFinset.card ≤ cap :=
    Nat.le_trans (List.toFinset_card_le _) (by simp)
  have hvl := listVcnt_le_length hiv
  unfold NODE_STRIDE at hbase
  omega

theorem listIsv_bound_of_tree {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap par pp : ℕ}
    {q : AuxTree} (hq : TreeMemMatch w h L mem nodesBase cap q par pp)
    {u : ℕ} (hu : u ∈ q.toList) :
    nodeField mem nodesBase u OFF_ISV ≤ 1 := by
  induction q generalizing par pp with
  | leaf => simp [AuxTree.toList] at hu
  | node y l r ihl ihr =>
      rcases hq with ⟨_, _, _, _, _, _, _, hiv, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hm | rfl) | hm
      · exact ihl hl hm
      · exact hiv
      · exact ihr hr hm

private theorem treeMemMatch_node_pull_data {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {q : AuxTree} {par_q pp_q u : ℕ}
    (hq : TreeMemMatch w h L mem nodesBase cap q par_q pp_q) (hu : u ∈ q.toList) :
    1 ≤ u ∧ u ≤ cap ∧
    nodeField mem nodesBase u OFF_ISV ≤ 1 ∧ nodeField mem nodesBase u OFF_HASE ≤ 1 ∧
    nodeField mem nodesBase u OFF_ISV + nodeField mem nodesBase u OFF_HASE ≤ 1 ∧
    nodeField mem nodesBase u OFF_DIR ≤ 1 ∧
    nodeField mem nodesBase u OFF_EU < 2 ^ w ∧ nodeField mem nodesBase u OFF_EV < 2 ^ w ∧
    nodeField mem nodesBase u OFF_EID < 2 ^ w ∧
    (nodeField mem nodesBase u OFF_HASE = 1 →
      let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
      let hp := mem (nodesBase - 1)
      NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_FLOW_PTR) ∧
      NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_AF_PTR) ∧
      NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_AB_PTR) ∧
      NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_COST_FWD) ∧
      NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_COST_BWD) ∧
      intVal mem (nodeField mem nodesBase u OFF_COST_BWD) h L =
        wrap h L (-intVal mem (nodeField mem nodesBase u OFF_COST_FWD) h L)) ∧
    (nodeField mem nodesBase u OFF_HASE = 0 →
      nodeField mem nodesBase u OFF_DIR = 0 ∧ nodeField mem nodesBase u OFF_FLOW_PTR = 0 ∧
      nodeField mem nodesBase u OFF_AF_PTR = 0 ∧ nodeField mem nodesBase u OFF_AB_PTR = 0 ∧
      nodeField mem nodesBase u OFF_COST_FWD = 0 ∧ nodeField mem nodesBase u OFF_COST_BWD = 0) ∧
    (nodeField mem nodesBase u OFF_HAS_TAG = 0 →
      nodeField mem nodesBase u OFF_TAG_PTR = 0 ∧ nodeField mem nodesBase u OFF_TAG_NEG = 0) := by
  induction q generalizing par_q pp_q with
  | leaf => simp [AuxTree.toList] at hu
  | node id l r ihl ihr =>
      rcases hq with ⟨h1, h2, _, _, _, _, _, hiv, hhe, hsum, hdir, _, _, heu, hev, heid,
        he1, he0, _, _, _, ht0, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hm | rfl) | hm
      · exact ihl hl hm
      · exact ⟨h1, h2, hiv, hhe, hsum, hdir, heu, hev, heid, he1, he0, ht0⟩
      · exact ihr hr hm

/-- Build `PullPre` on node `u` in `mem` using `IsNonStructNonAggOff` and heap agreement
from an arbitrary ambient `TreeMemMatch` `src`. -/
theorem pullPre_of_nonStruct_agree {w h L : ℕ} {mem₀ mem : ℕ → ℕ} {nodesBase cap u : ℕ}
    {src l r : AuxTree} {par_src pp_src par pp : ℕ}
    (hsrc : TreeMemMatch w h L mem₀ nodesBase cap src par_src pp_src) (hu : u ∈ src.toList)
    (hle : mem₀ (nodesBase - 1) ≤ mem (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
      mem a = mem₀ a)
    (hns : ∀ off, IsNonStructNonAggOff off →
      nodeField mem nodesBase u off = nodeField mem₀ nodesBase u off)
    (hL : nodeField mem nodesBase u OFF_LEFT = l.rootId)
    (hR : nodeField mem nodesBase u OFF_RIGHT = r.rootId)
    (hP : nodeField mem nodesBase u OFF_PARENT = par)
    (hPP : nodeField mem nodesBase u OFF_PPAR = pp)
    (hrev0 : nodeField mem₀ nodesBase u OFF_REV = 0)
    (hht0 : nodeField mem₀ nodesBase u OFF_HAS_TAG = 0)
    (hl : TreeMemMatch w h L mem nodesBase cap l u 0)
    (hr : TreeMemMatch w h L mem nodesBase cap r u 0)
    (hvc : listVcnt mem nodesBase
      (l.evalInorder (revFlag mem nodesBase) false ++ [u] ++
        r.evalInorder (revFlag mem nodesBase) false) < 2 ^ w) :
    PullPre w h L mem nodesBase cap u l r par pp := by
  obtain ⟨hu1, hu2, hiv, hhe, hsum, hdir, heu, hev, heid, he1, he0, ht0⟩ :=
    treeMemMatch_node_pull_data hsrc hu
  obtain ⟨htp0, htn0⟩ := ht0 hht0
  refine
    { hx1 := hu1, hx2 := hu2, hL := hL, hR := hR, hP := hP, hPP := hPP
      hrev0 := by rw [hns OFF_REV (by decide)]; exact hrev0
      hiv := by rw [hns OFF_ISV (by decide)]; exact hiv
      hhe := by rw [hns OFF_HASE (by decide)]; exact hhe
      hsum := by rw [hns OFF_ISV (by decide), hns OFF_HASE (by decide)]; exact hsum
      hdir := by rw [hns OFF_DIR (by decide)]; exact hdir
      hht0 := by rw [hns OFF_HAS_TAG (by decide)]; exact hht0
      htp0 := by rw [hns OFF_TAG_PTR (by decide)]; exact htp0
      htn0 := by rw [hns OFF_TAG_NEG (by decide)]; exact htn0
      heu := by rw [hns OFF_EU (by decide)]; exact heu
      hev := by rw [hns OFF_EV (by decide)]; exact hev
      heid := by rw [hns OFF_EID (by decide)]; exact heid
      he1 := ?_, he0 := ?_, hl := hl, hr := hr, hvcnt_lt := hvc }
  · rw [hns OFF_HASE (by decide), hns OFF_FLOW_PTR (by decide), hns OFF_AF_PTR (by decide),
        hns OFF_AB_PTR (by decide), hns OFF_COST_FWD (by decide), hns OFF_COST_BWD (by decide)]
    intro h1
    obtain ⟨kfl, kaf, kab, kcf, kcb, hcw⟩ := he1 h1
    refine ⟨numPtrOk_congr hle hheap kfl, numPtrOk_congr hle hheap kaf,
      numPtrOk_congr hle hheap kab, numPtrOk_congr hle hheap kcf,
      numPtrOk_congr hle hheap kcb, ?_⟩
    rw [intVal_agree_heap hheap kcb.2.1 kcb.2.2.1, intVal_agree_heap hheap kcf.2.1 kcf.2.2.1]
    exact hcw
  · rw [hns OFF_HASE (by decide), hns OFF_DIR (by decide), hns OFF_FLOW_PTR (by decide),
        hns OFF_AF_PTR (by decide), hns OFF_AB_PTR (by decide), hns OFF_COST_FWD (by decide),
        hns OFF_COST_BWD (by decide)]
    exact he0

theorem setChildAndParentStmt_runs {w nodesBase cap : ℕ} (p : Program) (st : State)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    {pPtr pVal bVal : ℕ} (childOff : ℕ)
    (hpPtr : st.regs 4 = pPtr) (hb : st.regs 9 = bVal) (hp : st.regs 3 = pVal) (hr0 : st.regs 0 = nodesBase)
    (hp_addr : pPtr + childOff < 2 ^ w)
    (hb_bound : bVal ≠ 0 → 1 ≤ bVal ∧ bVal ≤ cap) :
    ∀ ω, ∃ st' c,
      Runs w p ω (setChildAndParentStmt 4 childOff 9 3 10) st .normal st' c ∧
      c ≤ 20 ∧
      st'.pos = st.pos ∧
      (∀ r < 10, st'.regs r = st.regs r) ∧
      (if bVal = 0 then
         st'.mem = Function.update st.mem (pPtr + childOff) bVal
       else
         st'.mem = Function.update (Function.update st.mem (pPtr + childOff) bVal)
           (nodesBase + NODE_STRIDE * bVal + OFF_PARENT) pVal) := by
  intro ω
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  let mem1 := Function.update st.mem (pPtr + childOff) bVal
  let st1 : State := { mem := mem1, regs := st.regs, pos := st.pos }
  have hs1 : Runs w p ω (Stmt.store (fieldAddrExpr 4 childOff) (.reg 9)) st .normal st1
      ((fieldAddrExpr 4 childOff).size + (Expr.reg 9).size + 1) :=
    runs_store_iff.mpr ⟨pPtr + childOff, bVal,
      eval_fieldAddrExpr hpPtr hp_addr, Expr.eval_reg_of_eq hb, rfl, rfl, rfl⟩
  by_cases hbz : bVal = 0
  · let st2 := st1
    have hcond : Runs w p ω
        (Stmt.cond (.reg 9)
          (Stmt.assign 10 (nodePtrExpr 0 9) ;;
           Stmt.store (fieldAddrExpr 10 OFF_PARENT) (.reg 3)) Stmt.nop)
        st1 .normal st2 (1 + 1 + 1) :=
      runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (w := w) (by simpa [st1, hbz] using hb),
        by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    refine ⟨st2, _, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hs1, hcond, rfl⟩),
      (by simp [fieldAddrExpr, Expr.size]), rfl, fun _ _ => rfl, by simp [hbz, st2, st1, mem1]⟩
  · rcases hb_bound hbz with ⟨hb1, hb2⟩
    have hb_ptr_lt : nodesBase + NODE_STRIDE * bVal < 2 ^ w := nodePtr_lt_pow hbase hb2
    have hb_par_lt : nodesBase + NODE_STRIDE * bVal + OFF_PARENT < 2 ^ w :=
      nodeAddr_lt_pow hbase hb2 (by decide)
    let st2 : State := { mem := mem1, regs := Function.update st.regs 10 (nodesBase + NODE_STRIDE * bVal), pos := st.pos }
    let mem3 := Function.update mem1 (nodesBase + NODE_STRIDE * bVal + OFF_PARENT) pVal
    let st3 : State := { mem := mem3, regs := st2.regs, pos := st.pos }
    have ha2 : Runs w p ω (Stmt.assign 10 (nodePtrExpr 0 9)) st1 .normal st2
        ((nodePtrExpr 0 9).size + 1) :=
      runs_assign_iff.mpr ⟨nodesBase + NODE_STRIDE * bVal,
        eval_nodePtrExpr hstride (by simpa [st1] using hr0) (by simpa [st1] using hb) hb_ptr_lt,
        rfl, rfl, rfl⟩
    have ha3 : Runs w p ω (Stmt.store (fieldAddrExpr 10 OFF_PARENT) (.reg 3)) st2 .normal st3
        ((fieldAddrExpr 10 OFF_PARENT).size + (Expr.reg 3).size + 1) :=
      runs_store_iff.mpr ⟨nodesBase + NODE_STRIDE * bVal + OFF_PARENT, pVal,
        eval_fieldAddrExpr (by simp [st2]) hb_par_lt,
        Expr.eval_reg_of_eq (by simp [st2, hp]), rfl, rfl, rfl⟩
    have hbr : Runs w p ω
        (Stmt.assign 10 (nodePtrExpr 0 9) ;;
         Stmt.store (fieldAddrExpr 10 OFF_PARENT) (.reg 3))
        st1 .normal st3 _ :=
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, ha2, ha3, rfl⟩)
    have hcond : Runs w p ω
        (Stmt.cond (.reg 9)
          (Stmt.assign 10 (nodePtrExpr 0 9) ;;
           Stmt.store (fieldAddrExpr 10 OFF_PARENT) (.reg 3)) Stmt.nop)
        st1 .normal st3 _ :=
      runs_cond_iff.mpr ⟨bVal, _, Expr.eval_reg_of_eq (w := w) (by simpa [st1] using hb),
        by simpa [hbz] using hbr, rfl⟩
    refine ⟨st3, _, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hs1, hcond, rfl⟩),
      (by simp [nodePtrExpr, fieldAddrExpr, Expr.size]), rfl,
      fun r hr => by simp [st3, st2, Function.update_of_ne (by omega : r ≠ 10)],
      by simp [hbz, st3, mem3, mem1]⟩

theorem rotateBody_zero_runs {w nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (pos x : ℕ)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx : x ≤ cap) (hpar0 : nodeField mem₀ nodesBase x OFF_PARENT = 0) (ω : ℕ → Bool) :
    ∃ st' c,
      Runs w p ω (rotateBody sp) (startState [nodesBase, x] mem₀ pos) (.returned 0) st' c ∧
      c ≤ 20 ∧
      st'.mem = mem₀ := by
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  have hw0 : (0 : ℕ) < 2 ^ w := Nat.pow_pos (by decide)
  have hptr_lt : nodesBase + NODE_STRIDE * x < 2 ^ w := nodePtr_lt_pow hbase hx
  have hal_p : nodesBase + NODE_STRIDE * x + OFF_PARENT < 2 ^ w :=
    nodeAddr_lt_pow hbase hx (by decide)
  let st0 := startState [nodesBase, x] mem₀ pos
  let st1 : State := { mem := mem₀, regs := Function.update st0.regs 2 (nodesBase + NODE_STRIDE * x), pos := pos }
  let st2 : State := { mem := mem₀, regs := Function.update st1.regs 3 0, pos := pos }
  have ha1 : Runs w p ω (Stmt.assign 2 (nodePtrExpr 0 1)) st0 .normal st1
      ((nodePtrExpr 0 1).size + 1) :=
    runs_assign_iff.mpr ⟨nodesBase + NODE_STRIDE * x,
      eval_nodePtrExpr hstride rfl rfl hptr_lt, rfl, rfl, rfl⟩
  have hload : (fieldLoadExpr 2 OFF_PARENT).eval w st1 = some 0 := by
    rw [eval_fieldLoadExpr (by simp [st1] : st1.regs 2 = nodesBase + NODE_STRIDE * x) hal_p]
    simpa [st1, st0, nodeField] using hpar0
  have ha2 : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT)) st1 .normal st2
      ((fieldLoadExpr 2 OFF_PARENT).size + 1) :=
    runs_assign_iff.mpr ⟨0, hload, rfl, rfl, rfl⟩
  have hret : Runs w p ω (Stmt.ret (.const 0)) st2 (.returned 0) st2 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩
  dsimp only [rotateBody]
  refine ⟨st2, _, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha1,
    runs_seq_iff.mpr (Or.inr ⟨st2, _, _, ha2,
      runs_cond_iff.mpr ⟨0, 2, Expr.eval_reg_of_eq (by simp [st2]), by simpa using hret, rfl⟩, rfl⟩), rfl⟩),
    ?_, rfl⟩
  simp only [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size]
  omega

theorem rotatePrefix_exec {w nodesBase cap x p_id g_id pp_p : ℕ}
    (pr : Program) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx2 : x ≤ cap) (hp1 : 1 ≤ p_id) (hp2 : p_id ≤ cap)
    (hx_par : nodeField mem₀ nodesBase x OFF_PARENT = p_id)
    (hp_par : nodeField mem₀ nodesBase p_id OFF_PARENT = g_id)
    (hp_pp : nodeField mem₀ nodesBase p_id OFF_PPAR = pp_p) :
    ∀ s_tail ω o st_f c_tail,
      let ptrX := nodesBase + NODE_STRIDE * x
      let ptrP := nodesBase + NODE_STRIDE * p_id
      let pRight := nodeField mem₀ nodesBase p_id OFF_RIGHT
      let mem_pre := Function.update (Function.update mem₀ (ptrX + OFF_PPAR) pp_p) (ptrP + OFF_PPAR) 0
      Runs w pr ω s_tail
        { mem := mem_pre,
          regs := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update
              (startState [nodesBase, x] mem₀ pos).regs 2 ptrX) 3 p_id) 4 ptrP) 5 g_id) 6 pp_p) 7 pRight) 8
            (if x = pRight then 1 else 0),
          pos := pos } o st_f c_tail →
      ∃ c_full, c_full ≤ c_tail + 60 ∧
        Runs w pr ω
          (Stmt.assign 2 (nodePtrExpr 0 1) ;;
           Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT) ;;
           Stmt.cond (.reg 3)
             (Stmt.assign 4 (nodePtrExpr 0 3) ;;
              Stmt.assign 5 (fieldLoadExpr 4 OFF_PARENT) ;;
              Stmt.assign 6 (fieldLoadExpr 4 OFF_PPAR) ;;
              Stmt.store (fieldAddrExpr 2 OFF_PPAR) (.reg 6) ;;
              Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.const 0) ;;
              Stmt.assign 7 (fieldLoadExpr 4 OFF_RIGHT) ;;
              Stmt.assign 8 (.bin .eq (.reg 1) (.reg 7)) ;;
              s_tail)
             (Stmt.ret (.const 0)))
          (startState [nodesBase, x] mem₀ pos) o st_f c_full := by
  intro s_tail ω o st_f c_tail
  dsimp only
  intro htail
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  have hw0 : (0 : ℕ) < 2 ^ w := Nat.pow_pos (by decide)
  let ptrX := nodesBase + NODE_STRIDE * x
  let ptrP := nodesBase + NODE_STRIDE * p_id
  let pRight := nodeField mem₀ nodesBase p_id OFF_RIGHT
  have hx_ptr_lt : ptrX < 2 ^ w := nodePtr_lt_pow hbase hx2
  have hp_ptr_lt : ptrP < 2 ^ w := nodePtr_lt_pow hbase hp2
  have hx_par_lt : ptrX + OFF_PARENT < 2 ^ w := nodeAddr_lt_pow hbase hx2 (by decide)
  have hx_pp_lt : ptrX + OFF_PPAR < 2 ^ w := nodeAddr_lt_pow hbase hx2 (by decide)
  have hp_par_lt : ptrP + OFF_PARENT < 2 ^ w := nodeAddr_lt_pow hbase hp2 (by decide)
  have hp_pp_lt : ptrP + OFF_PPAR < 2 ^ w := nodeAddr_lt_pow hbase hp2 (by decide)
  have hp_r_lt : ptrP + OFF_RIGHT < 2 ^ w := nodeAddr_lt_pow hbase hp2 (by decide)
  let st0 := startState [nodesBase, x] mem₀ pos
  let st1 : State := { mem := mem₀, regs := Function.update st0.regs 2 ptrX, pos := pos }
  let st2 : State := { mem := mem₀, regs := Function.update st1.regs 3 p_id, pos := pos }
  let st3 : State := { mem := mem₀, regs := Function.update st2.regs 4 ptrP, pos := pos }
  let st4 : State := { mem := mem₀, regs := Function.update st3.regs 5 g_id, pos := pos }
  let st5 : State := { mem := mem₀, regs := Function.update st4.regs 6 pp_p, pos := pos }
  let mem6 := Function.update mem₀ (ptrX + OFF_PPAR) pp_p
  let st6 : State := { mem := mem6, regs := st5.regs, pos := pos }
  let mem7 := Function.update mem6 (ptrP + OFF_PPAR) 0
  let st7 : State := { mem := mem7, regs := st5.regs, pos := pos }
  let st8 : State := { mem := mem7, regs := Function.update st5.regs 7 pRight, pos := pos }
  have hpR7 : mem7 (ptrP + OFF_RIGHT) = pRight := by
    have h76 : mem7 (ptrP + OFF_RIGHT) = mem6 (ptrP + OFF_RIGHT) :=
      Function.update_of_ne (fun h => absurd (Nat.add_left_cancel h) (by decide)) _ _
    have h60 : mem6 (ptrP + OFF_RIGHT) = mem₀ (ptrP + OFF_RIGHT) := by
      by_cases hxp : x = p_id
      · subst hxp; exact Function.update_of_ne (fun h => absurd (Nat.add_left_cancel h) (by decide)) _ _
      · exact Function.update_of_ne (node_field_addr_ne hxp (by decide) (by decide)).symm _ _
    exact h76.trans h60
  have ha1 : Runs w pr ω (Stmt.assign 2 (nodePtrExpr 0 1)) st0 .normal st1
      ((nodePtrExpr 0 1).size + 1) :=
    runs_assign_iff.mpr ⟨ptrX, eval_nodePtrExpr hstride rfl rfl hx_ptr_lt, rfl, rfl, rfl⟩
  have ha2 : Runs w pr ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT)) st1 .normal st2
      ((fieldLoadExpr 2 OFF_PARENT).size + 1) := by
    refine runs_assign_iff.mpr ⟨p_id, ?_, rfl, rfl, rfl⟩
    rw [eval_fieldLoadExpr (by simp [st1]) hx_par_lt]
    simpa [st1, st0, nodeField] using hx_par
  have ha3 : Runs w pr ω (Stmt.assign 4 (nodePtrExpr 0 3)) st2 .normal st3
      ((nodePtrExpr 0 3).size + 1) :=
    runs_assign_iff.mpr ⟨ptrP, eval_nodePtrExpr hstride (by simp [st2, st1, st0]; rfl) (by simp [st2]) hp_ptr_lt,
      rfl, rfl, rfl⟩
  have ha4 : Runs w pr ω (Stmt.assign 5 (fieldLoadExpr 4 OFF_PARENT)) st3 .normal st4
      ((fieldLoadExpr 4 OFF_PARENT).size + 1) := by
    refine runs_assign_iff.mpr ⟨g_id, ?_, rfl, rfl, rfl⟩
    rw [eval_fieldLoadExpr (by simp [st3]) hp_par_lt]
    simpa [st3, st2, st1, st0, nodeField] using hp_par
  have ha5 : Runs w pr ω (Stmt.assign 6 (fieldLoadExpr 4 OFF_PPAR)) st4 .normal st5
      ((fieldLoadExpr 4 OFF_PPAR).size + 1) := by
    refine runs_assign_iff.mpr ⟨pp_p, ?_, rfl, rfl, rfl⟩
    rw [eval_fieldLoadExpr (by simp [st4, st3]) hp_pp_lt]
    simpa [st4, st3, st2, st1, st0, nodeField] using hp_pp
  have hs6 : Runs w pr ω (Stmt.store (fieldAddrExpr 2 OFF_PPAR) (.reg 6)) st5 .normal st6
      ((fieldAddrExpr 2 OFF_PPAR).size + (Expr.reg 6).size + 1) :=
    runs_store_iff.mpr ⟨ptrX + OFF_PPAR, pp_p,
      eval_fieldAddrExpr (by simp [st5, st4, st3, st2, st1]) hx_pp_lt,
      Expr.eval_reg_of_eq (by simp [st5]), rfl, rfl, rfl⟩
  have hs7 : Runs w pr ω (Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.const 0)) st6 .normal st7
      ((fieldAddrExpr 4 OFF_PPAR).size + (Expr.const 0).size + 1) :=
    runs_store_iff.mpr ⟨ptrP + OFF_PPAR, 0,
      eval_fieldAddrExpr (by simp [st6, st5, st4, st3]) hp_pp_lt, Expr.eval_const hw0, rfl, rfl, rfl⟩
  have ha8 : Runs w pr ω (Stmt.assign 7 (fieldLoadExpr 4 OFF_RIGHT)) st7 .normal st8
      ((fieldLoadExpr 4 OFF_RIGHT).size + 1) := by
    refine runs_assign_iff.mpr ⟨pRight, ?_, rfl, rfl, rfl⟩
    rw [eval_fieldLoadExpr (by simp [st7, st5, st4, st3]) hp_r_lt]
    simpa [st7] using hpR7
  have ha9 : Runs w pr ω (Stmt.assign 8 (.bin .eq (.reg 1) (.reg 7))) st8 .normal
      { mem := mem7, regs := Function.update st8.regs 8 (if x = pRight then 1 else 0), pos := pos }
      ((Expr.bin .eq (.reg 1) (.reg 7)).size + 1) :=
    runs_assign_iff.mpr ⟨if x = pRight then 1 else 0,
      Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [st8, st5, st4, st3, st2, st1, st0]; rfl))
        (Expr.eval_reg_of_eq (by simp [st8])) (by unfold NODE_STRIDE at hbase; omega),
      rfl, rfl, rfl⟩
  have hbranch : Runs w pr ω
      (Stmt.assign 4 (nodePtrExpr 0 3) ;;
       Stmt.assign 5 (fieldLoadExpr 4 OFF_PARENT) ;;
       Stmt.assign 6 (fieldLoadExpr 4 OFF_PPAR) ;;
       Stmt.store (fieldAddrExpr 2 OFF_PPAR) (.reg 6) ;;
       Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.const 0) ;;
       Stmt.assign 7 (fieldLoadExpr 4 OFF_RIGHT) ;;
       Stmt.assign 8 (.bin .eq (.reg 1) (.reg 7)) ;;
       s_tail) st2 o st_f _ :=
    runs_seq_iff.mpr (Or.inr ⟨st3, _, _, ha3,
      runs_seq_iff.mpr (Or.inr ⟨st4, _, _, ha4,
        runs_seq_iff.mpr (Or.inr ⟨st5, _, _, ha5,
          runs_seq_iff.mpr (Or.inr ⟨st6, _, _, hs6,
            runs_seq_iff.mpr (Or.inr ⟨st7, _, _, hs7,
              runs_seq_iff.mpr (Or.inr ⟨st8, _, _, ha8,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha9, htail, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hcond : Runs w pr ω
      (Stmt.cond (.reg 3)
        (Stmt.assign 4 (nodePtrExpr 0 3) ;;
         Stmt.assign 5 (fieldLoadExpr 4 OFF_PARENT) ;;
         Stmt.assign 6 (fieldLoadExpr 4 OFF_PPAR) ;;
         Stmt.store (fieldAddrExpr 2 OFF_PPAR) (.reg 6) ;;
         Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.const 0) ;;
         Stmt.assign 7 (fieldLoadExpr 4 OFF_RIGHT) ;;
         Stmt.assign 8 (.bin .eq (.reg 1) (.reg 7)) ;;
         s_tail)
        (Stmt.ret (.const 0))) st2 o st_f _ :=
    runs_cond_iff.mpr ⟨p_id, _, Expr.eval_reg_of_eq (by simp [st2]),
      by simpa [show p_id ≠ 0 by omega] using hbranch, rfl⟩
  have hfull : Runs w pr ω
      (Stmt.assign 2 (nodePtrExpr 0 1) ;;
       Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT) ;;
       Stmt.cond (.reg 3) _ (Stmt.ret (.const 0))) st0 o st_f _ :=
    runs_seq_iff.mpr (Or.inr ⟨st1, _, _, ha1, runs_seq_iff.mpr (Or.inr ⟨st2, _, _, ha2, hcond, rfl⟩), rfl⟩)
  refine ⟨_, ?_, hfull⟩
  simp only [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size]
  omega

end

end MinCostFlow.LinkCut.Prog
