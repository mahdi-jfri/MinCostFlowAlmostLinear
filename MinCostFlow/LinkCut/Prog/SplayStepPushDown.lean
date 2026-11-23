module

public import MinCostFlow.LinkCut.Prog.SplayStepPushDownBlocks

namespace MinCostFlow.LinkCut.Prog

/-!
Word-RAM specification for `pushDownBody`:
- `pushDownRevBranch_runs` and `pushDownTagBranch_runs` for lazy rev and tag propagation,
- `pushDownBody_runs_subtree` preserving `TreeMemMatch`, `evalMemSteps`, `evalInorder`,
  outside-subtree fields, static payload offsets, and `LctFrame`,
- `pushDownBody_runs_in_tree` lifting the subtree update into any ambient `AuxTree`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

private theorem pushDownRevBranch_runs {w h L nodesBase cap x parId pp : ℕ}
    {p : Program} {sp : SplayProcs} {mem₀ : ℕ → ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (st0 : State)
    (hmem0 : st0.mem = mem₀)
    (hr0 : st0.regs 0 = nodesBase)
    (hr2 : st0.regs 2 = nodesBase + NODE_STRIDE * x)
    {l r : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap (.node x l r) parId pp)
    (hnd : (AuxTree.node x l r).toList.Nodup)
    (hrev1 : nodeField mem₀ nodesBase x OFF_REV ≠ 0) :
    ∀ ω, ∃ st' c,
      Runs w p ω
        (Stmt.assign 4 (fieldLoadExpr 2 OFF_LEFT) ;;
         Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
         Stmt.assign 4 (fieldLoadExpr 2 OFF_RIGHT) ;;
         Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
         Stmt.store (fieldAddrExpr 2 OFF_REV) (.const 0))
        st0 .normal st' c ∧
      c ≤ 2 * K_REV_NODE + 40 ∧
      st'.regs 0 = nodesBase ∧
      st'.regs 2 = nodesBase + NODE_STRIDE * x ∧
      st'.mem (nodesBase - 1) = mem₀ (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap (.node x l.revRoot r.revRoot) parId pp ∧
      evalMemSteps st'.mem nodesBase h L (.node x l.revRoot r.revRoot) false 0 =
        evalMemSteps mem₀ nodesBase h L (.node x l r) false 0 ∧
      (AuxTree.node x l.revRoot r.revRoot).evalInorder (revFlag st'.mem nodesBase) false =
        (AuxTree.node x l r).evalInorder (revFlag mem₀ nodesBase) false ∧
      revFlag st'.mem nodesBase x = false ∧
      (∀ u ≤ cap, u ∉ (AuxTree.node x l r).toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        mem₀ st'.mem := by
  subst hmem0
  intro ω
  rcases nodup_node_split hnd with ⟨hl_nd, hr_nd, hx_l, hx_r, hdisj⟩
  have htx := ht
  rcases ht with ⟨hx1, hx2, hL, hR, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, hl_m, hr_m⟩
  have hw0 : (0 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  let ptr := nodesBase + NODE_STRIDE * x
  have hl_ne_x : x ≠ l.rootId := nodeId_ne_rootId_of_not_mem hx1 hx_l
  have hr_ne_x : x ≠ r.rootId := nodeId_ne_rootId_of_not_mem hx1 hx_r
  rcases revChild_exec hp_ok hbase hx2 (by decide) st0 hr0 hr2 hL hl_m hl_nd ω with
    ⟨st2, c_l, hr_l, hc_l, hr2_0, hr2_2, hm2_l, hsteps2_l, heval2_l, hhp2, hstat2, hout2, hpres2⟩
  have hmem2_x : ∀ off < NODE_STRIDE,
      nodeField st2.mem nodesBase x off = nodeField st0.mem nodesBase x off := fun off hoff =>
    nodeField_eq_of_outside_slot hl_ne_x hoff hout2
  have hmem2_r : ∀ u ∈ r.toList, ∀ off < NODE_STRIDE,
      nodeField st2.mem nodesBase u off = nodeField st0.mem nodesBase u off := fun u hu off hoff =>
    nodeField_eq_of_outside_slot
      (nodeId_ne_rootId_of_not_mem (hr_m.nodup_perm_mem hu).1 (fun h => hdisj h hu)) hoff hout2
  have hheap2 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < st0.mem (nodesBase - 1) →
      st2.mem a = st0.mem a := fun a ha _ => hpres2 a (Or.inr ha)
  have hr2_m : TreeMemMatch w h L st2.mem nodesBase cap r x 0 :=
    memAgree_treeMemMatch_of_nodeList hr_m hmem2_r (by rw [hhp2]) hheap2
  have hR2 : nodeField st2.mem nodesBase x OFF_RIGHT = r.rootId :=
    (hmem2_x OFF_RIGHT (by decide)).trans hR
  rcases revChild_exec hp_ok hbase hx2 (by decide) st2 hr2_0 hr2_2 hR2 hr2_m hr_nd ω with
    ⟨st4, c_r, hr_r, hc_r, hr4_0, hr4_2, hm4_r, hsteps4_r, heval4_r, hhp4, hstat4, hout4, hpres4⟩
  let st5 : State := { mem := Function.update st4.mem (ptr + OFF_REV) 0, regs := st4.regs, pos := st4.pos }
  have hst5_r : Runs w p ω (Stmt.store (fieldAddrExpr 2 OFF_REV) (.const 0)) st4 .normal st5 5 :=
    runs_store_iff.mpr ⟨ptr + OFF_REV, 0,
      eval_fieldAddrExpr hr4_2 (nodeAddr_lt_pow hbase hx2 (by decide)), Expr.eval_const hw0, rfl, rfl, rfl⟩
  have hrun : Runs w p ω
      (Stmt.assign 4 (fieldLoadExpr 2 OFF_LEFT) ;;
       Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
       Stmt.assign 4 (fieldLoadExpr 2 OFF_RIGHT) ;;
       Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
       Stmt.store (fieldAddrExpr 2 OFF_REV) (.const 0))
      st0 .normal st5 (c_l + (c_r + 5 + 1) + 1) :=
    runs_seq2_normal hr_l (runs_seq2_normal hr_r hst5_r)
  have hmem4_x : ∀ off < NODE_STRIDE,
      nodeField st4.mem nodesBase x off = nodeField st0.mem nodesBase x off := fun off hoff =>
    (nodeField_eq_of_outside_slot hr_ne_x hoff hout4).trans (hmem2_x off hoff)
  have hmem5_x_rev : nodeField st5.mem nodesBase x OFF_REV = 0 :=
    nodeField_update_self st4.mem nodesBase x OFF_REV 0
  have hmem5_x_other : ∀ off < NODE_STRIDE, off ≠ OFF_REV →
      nodeField st5.mem nodesBase x off = nodeField st0.mem nodesBase x off := fun off hoff hne =>
    (nodeField_update_ne_off hne.symm).trans (hmem4_x off hoff)
  have hmem5_l : ∀ u ∈ l.revRoot.toList, ∀ off < NODE_STRIDE,
      nodeField st5.mem nodesBase u off = nodeField st2.mem nodesBase u off := fun u hu off hoff => by
    have hu' : u ∈ l.toList := l.revRoot_toList_perm.mem_iff.1 hu
    have hu_pos := (hl_m.nodup_perm_mem hu').1
    have hu_ne_x : u ≠ x := fun h => hx_l (h ▸ hu')
    have hu_ne_r : u ≠ r.rootId := nodeId_ne_rootId_of_not_mem hu_pos (fun h => hdisj hu' h)
    exact (nodeField_update_ne_node hu_ne_x.symm (by decide) hoff).trans
      (nodeField_eq_of_outside_slot hu_ne_r hoff hout4)
  have hmem5_r : ∀ u ∈ r.revRoot.toList, ∀ off < NODE_STRIDE,
      nodeField st5.mem nodesBase u off = nodeField st4.mem nodesBase u off := fun u hu off hoff => by
    have hu' : u ∈ r.toList := r.revRoot_toList_perm.mem_iff.1 hu
    have hu_ne_x : u ≠ x := fun h => hx_r (h ▸ hu')
    exact nodeField_update_ne_node hu_ne_x.symm (by decide) hoff
  have hhp4' : st4.mem (nodesBase - 1) = st0.mem (nodesBase - 1) := hhp4.trans hhp2
  have hhp5 : st5.mem (nodesBase - 1) = st0.mem (nodesBase - 1) := by
    have hmul : NODE_STRIDE * 1 ≤ NODE_STRIDE * x := Nat.mul_le_mul_left NODE_STRIDE hx1
    have hne : ptr + OFF_REV ≠ nodesBase - 1 := by
      dsimp [ptr]; unfold OFF_REV NODE_STRIDE at *; omega
    dsimp [st5]
    rw [Function.update_of_ne hne.symm]
    exact hhp4'
  have hpres05 : MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      st0.mem st5.mem := by
    have hlo : nodesBase + NODE_STRIDE ≤ ptr + OFF_REV := by
      have hmul : NODE_STRIDE * 1 ≤ NODE_STRIDE * x := Nat.mul_le_mul_left NODE_STRIDE hx1
      dsimp [ptr]; unfold OFF_REV NODE_STRIDE at *; omega
    have hhi : ptr + OFF_REV < nodesBase + NODE_STRIDE * (cap + 1) := by
      have hmul := Nat.mul_le_mul_left NODE_STRIDE hx2
      dsimp [ptr]; rw [Nat.mul_add, Nat.mul_one]; unfold OFF_REV NODE_STRIDE at *; omega
    exact memPreservedOutside_trans (memPreservedOutside_trans hpres2 hpres4)
      (memPreservedOutside_update hlo hhi)
  have hheap5 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < st0.mem (nodesBase - 1) →
      st5.mem a = st0.mem a := fun a ha _ => hpres05 a (Or.inr ha)
  have hheap25 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < st2.mem (nodesBase - 1) →
      st5.mem a = st2.mem a := fun a ha hlt => by
    rw [hheap5 a ha (by rw [← hhp2]; exact hlt), hheap2 a ha (by rw [← hhp2]; exact hlt)]
  have hheap45 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < st4.mem (nodesBase - 1) →
      st5.mem a = st4.mem a := fun a ha hlt => by
    rw [hheap5 a ha (by rw [← hhp4']; exact hlt), (memPreservedOutside_trans hpres2 hpres4) a (Or.inr ha)]
  have hm5_l : TreeMemMatch w h L st5.mem nodesBase cap l.revRoot x 0 :=
    memAgree_treeMemMatch_of_nodeList hm2_l hmem5_l (by rw [hhp5, hhp2]) hheap25
  have hm5_r : TreeMemMatch w h L st5.mem nodesBase cap r.revRoot x 0 :=
    memAgree_treeMemMatch_of_nodeList hm4_r hmem5_r (by rw [hhp5, ← hhp4']) hheap45
  have hsteps5_l : evalMemSteps st5.mem nodesBase h L l.revRoot false 0 =
      (evalMemSteps st0.mem nodesBase h L l false 0).reverse.map RawStep.flip :=
    (evalMemSteps_agree hm2_l hmem5_l hheap25 _ _).trans hsteps2_l
  have hsteps5_r : evalMemSteps st5.mem nodesBase h L r.revRoot false 0 =
      (evalMemSteps st0.mem nodesBase h L r false 0).reverse.map RawStep.flip := by
    rw [evalMemSteps_agree hm4_r hmem5_r hheap45, hsteps4_r, evalMemSteps_agree hr_m hmem2_r hheap2]
  have heval5_l : l.revRoot.evalInorder (revFlag st5.mem nodesBase) false =
      (l.evalInorder (revFlag st0.mem nodesBase) false).reverse :=
    (evalInorder_agree_of_list (fun u hu => hmem5_l u hu OFF_REV (by decide)) false).trans heval2_l
  have heval5_r : r.revRoot.evalInorder (revFlag st5.mem nodesBase) false =
      (r.evalInorder (revFlag st0.mem nodesBase) false).reverse := by
    rw [evalInorder_agree_of_list (fun u hu => hmem5_r u hu OFF_REV (by decide)), heval4_r,
      evalInorder_agree_of_list (fun u hu => hmem2_r u hu OFF_REV (by decide))]
  have hstat5 : ∀ u off, IsStaticPayloadOff off →
      nodeField st5.mem nodesBase u off = nodeField st0.mem nodesBase u off := fun u off hoff => by
    have h4 : nodeField st4.mem nodesBase u off = nodeField st0.mem nodesBase u off :=
      (hstat4 u off hoff).trans (hstat2 u off hoff)
    have hupd : nodeField st5.mem nodesBase u off = nodeField st4.mem nodesBase u off := by
      rcases isStaticPayloadOff_ne_struct hoff with ⟨hlo, _, _, _, _, hne_rev, _⟩
      by_cases hux : u = x
      · subst hux; exact nodeField_update_ne_off hne_rev.symm
      · exact nodeField_update_ne_node (fun h => hux h.symm) (by decide) hlo
    exact hupd.trans h4
  have hisv5 : ∀ u ∈ (AuxTree.node x l r).toList,
      nodeField st5.mem nodesBase u OFF_ISV = nodeField st0.mem nodesBase u OFF_ISV :=
    fun u _ => hstat5 u OFF_ISV (by simp [IsStaticPayloadOff])
  rcases pushDownPhase1_post htx hrev1 hm5_l hm5_r hsteps5_l hsteps5_r heval5_l heval5_r
      hmem5_x_rev hmem5_x_other hisv5 hhp5 hheap5 with
    ⟨hm_post, hsteps_post, heval_post, hrev_post⟩
  refine ⟨st5, _, hrun, by omega, hr4_0, hr4_2, hhp5, hm_post, hsteps_post, heval_post, hrev_post,
    ?_, fun u _ off hoff => hstat5 u off hoff, hpres05⟩
  intro u _ hu off hoff
  simp only [AuxTree.toList, List.mem_append, List.mem_singleton, not_or] at hu
  rcases hu with ⟨⟨hu_l, hu_x⟩, hu_r⟩
  by_cases hu0 : u = 0
  · subst hu0
    have hlt : nodesBase + NODE_STRIDE * 0 + off < nodesBase + NODE_STRIDE := by
      unfold NODE_STRIDE at hoff ⊢; omega
    exact hpres05 _ (Or.inl hlt)
  · have hu_pos : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu0
    have h54 : nodeField st5.mem nodesBase u off = nodeField st4.mem nodesBase u off :=
      nodeField_update_ne_node (fun h => hu_x h.symm) (by decide) hoff
    have h42 : nodeField st4.mem nodesBase u off = nodeField st2.mem nodesBase u off :=
      nodeField_eq_of_outside_slot (nodeId_ne_rootId_of_not_mem hu_pos hu_r) hoff hout4
    have h20 : nodeField st2.mem nodesBase u off = nodeField st0.mem nodesBase u off :=
      nodeField_eq_of_outside_slot (nodeId_ne_rootId_of_not_mem hu_pos hu_l) hoff hout2
    exact h54.trans (h42.trans h20)

private theorem pushDownTagBranch_runs {w h L nodesBase cap x parId pp : ℕ}
    {p : Program} {sp : SplayProcs} {mem₁ : ℕ → ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : mem₁ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₁ (nodesBase - 1))
    (hz : ZeroFrom mem₁ (mem₁ (nodesBase - 1)))
    (hhp_lt : mem₁ (nodesBase - 1) + 2 * K_APPLY_TAG L < 2 ^ w)
    (h0 : SlotZeroOk mem₁ nodesBase)
    (st1 : State)
    (hmem1 : st1.mem = mem₁)
    (hr0 : st1.regs 0 = nodesBase)
    (hr2 : st1.regs 2 = nodesBase + NODE_STRIDE * x)
    {l₁ r₁ : AuxTree} (ht : TreeMemMatch w h L mem₁ nodesBase cap (.node x l₁ r₁) parId pp)
    (hnd : (AuxTree.node x l₁ r₁).toList.Nodup)
    (hrev1 : revFlag mem₁ nodesBase x = false)
    (hht1_ne : nodeField mem₁ nodesBase x OFF_HAS_TAG ≠ 0) :
    ∀ ω, ∃ st' c,
      Runs w p ω
        (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
         Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
         Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
         Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
         Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0) ;;
         Stmt.assign 6 (fieldLoadExpr 2 OFF_LEFT) ;;
         Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5] ;;
         Stmt.assign 6 (fieldLoadExpr 2 OFF_RIGHT) ;;
         Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5])
        st1 .normal st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₁ (nodesBase - 1)) ≤ 2 * K_APPLY_TAG L + 60 ∧
      mem₁ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap (.node x l₁ r₁) parId pp ∧
      evalMemSteps st'.mem nodesBase h L (.node x l₁ r₁) false 0 =
        evalMemSteps mem₁ nodesBase h L (.node x l₁ r₁) false 0 ∧
      (AuxTree.node x l₁ r₁).evalInorder (revFlag st'.mem nodesBase) false =
        (AuxTree.node x l₁ r₁).evalInorder (revFlag mem₁ nodesBase) false ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      revFlag st'.mem nodesBase x = false ∧
      (∀ u ≤ cap, u ∉ (AuxTree.node x l₁ r₁).toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₁ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₁ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₁ st'.mem := by
  subst hmem1
  intro ω
  rcases nodup_node_split hnd with ⟨hl_nd, hr_nd, hx_l, hx_r, hdisj⟩
  have htx := ht
  rcases ht with ⟨hx1, hx2, hL, hR, _, _, _, _, _, _, _, hht_le, htn_le, _, _, _,
    _, _, _, _, htag1, _, _, _, _, _, _, hl_m, hr_m⟩
  have hht_eq1 : nodeField st1.mem nodesBase x OFF_HAS_TAG = 1 :=
    eq_one_of_le_one_ne_zero hht_le hht1_ne
  rcases htag1 hht_eq1 with ⟨htp_ok, _, d, hdmod, hfit⟩
  rw [hrev1] at hfit
  rcases stepsShiftFit_append.mp hfit with ⟨hfit_l, hfit_r⟩
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let tPtr := nodeField st1.mem nodesBase x OFF_TAG_PTR
  let tNeg := nodeField st1.mem nodesBase x OFF_TAG_NEG
  -- 1. clear tag fields
  rcases clearTagFields_exec hbase hx2 st1 hr0 hr2 ω with
    ⟨st2, c_clr, hr_clr, hc_clr, hr2_0, hr2_2, hr2_4, hr2_5, h2_ht, h2_tp, h2_tn, h2_other, h2_out⟩
  have h12_lt_hp : ∀ a, arenaHi ≤ a → st2.mem a = st1.mem a := fun a ha => by
    apply h2_out; right
    have hmul : NODE_STRIDE * x + NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left NODE_STRIDE hx2) _
    dsimp [arenaHi] at ha; omega
  have h12_nb_lt : ∀ a, a < nodesBase + NODE_STRIDE → st2.mem a = st1.mem a := fun a ha => by
    apply h2_out; left
    have hmul : NODE_STRIDE * 1 ≤ NODE_STRIDE * x := Nat.mul_le_mul_left NODE_STRIDE hx1
    omega
  have h2_hp : st2.mem (nodesBase - 1) = st1.mem (nodesBase - 1) :=
    h12_nb_lt _ (by unfold NODE_STRIDE; omega)
  have h2_L : st2.mem (nodesBase - 3) = L :=
    (h12_nb_lt _ (by unfold NODE_STRIDE; omega)).trans hL_hdr
  have h2_hz : ZeroFrom st2.mem (st2.mem (nodesBase - 1)) := by
    rw [h2_hp]; intro i hi; rw [h12_lt_hp i (le_trans harena hi)]; exact hz i hi
  have h2_0 : SlotZeroOk st2.mem nodesBase := fun off hoff =>
    (h12_nb_lt _ (by omega)).trans (h0 off hoff)
  have h2_lct : LctFrame (nodesBase + NODE_STRIDE) arenaHi (nodesBase - 1) st1.mem st2.mem :=
    ⟨by unfold NODE_STRIDE; omega, harena, by rw [h2_hp], hz, h2_hz, fun i hi => by
      rcases hi with ⟨hi1, _⟩ | ⟨hi1, _⟩
      · exact h12_nb_lt i hi1
      · exact h12_lt_hp i hi1⟩
  have h2_node : ∀ {u}, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField st2.mem nodesBase u off = nodeField st1.mem nodesBase u off :=
    fun hux off hoff => nodeField_eq_of_outside_slot hux hoff h2_out
  have h2_l_fields : ∀ u ∈ l₁.toList, ∀ off < NODE_STRIDE,
      nodeField st2.mem nodesBase u off = nodeField st1.mem nodesBase u off :=
    fun u hu => h2_node (fun h => hx_l (h ▸ hu))
  have h2_r_fields : ∀ u ∈ r₁.toList, ∀ off < NODE_STRIDE,
      nodeField st2.mem nodesBase u off = nodeField st1.mem nodesBase u off :=
    fun u hu => h2_node (fun h => hx_r (h ▸ hu))
  have h2_heap_lt : ∀ a, arenaHi ≤ a → a < st1.mem (nodesBase - 1) → st2.mem a = st1.mem a :=
    fun a ha _ => h12_lt_hp a ha
  have h2_ml : TreeMemMatch w h L st2.mem nodesBase cap l₁ x 0 :=
    memAgree_treeMemMatch_of_nodeList hl_m h2_l_fields (by omega) h2_heap_lt
  have h2_mr : TreeMemMatch w h L st2.mem nodesBase cap r₁ x 0 :=
    memAgree_treeMemMatch_of_nodeList hr_m h2_r_fields (by omega) h2_heap_lt
  have h2_tp_ok : NumPtrOk st2.mem arenaHi (st2.mem (nodesBase - 1)) h L tPtr := by
    rw [h2_hp]; exact numPtrOk_congr le_rfl h2_heap_lt htp_ok
  have h2_dmod : d % (capacity h L : ℤ) =
      (if tNeg = 0 then intVal st2.mem tPtr h L else -intVal st2.mem tPtr h L) % (capacity h L : ℤ) := by
    rw [intVal_agree_heap h2_heap_lt htp_ok.2.1 htp_ok.2.2.1, hdmod]
    simp only [nodeTagInt, hht_eq1, Nat.one_ne_zero, ↓reduceIte, optIntVal, htp_ok.1]
    rfl
  have h2_fit_l : StepsShiftFit h L (evalMemSteps st2.mem nodesBase h L l₁ false 0) d := by
    rw [evalMemSteps_agree hl_m h2_l_fields h2_heap_lt]; exact hfit_l
  have h2_L_eq : nodeField st2.mem nodesBase x OFF_LEFT = l₁.rootId :=
    (h2_other OFF_LEFT (by decide) (by decide) (by decide) (by decide)).trans hL
  -- 2. applyTag on l₁
  have h2_hp_lt : st2.mem (nodesBase - 1) + K_APPLY_TAG L < 2 ^ w := by
    rw [h2_hp]; omega
  rcases applyTagChild_exec hp_ok hbase hnb hx2 (by decide) st2 h2_L (by rw [h2_hp]; exact harena)
      h2_hz h2_hp_lt h2_0 hr2_0 hr2_2 hr2_4 hr2_5 h2_L_eq h2_ml hl_nd htn_le h2_tp_ok h2_dmod
      h2_fit_l ω with
    ⟨st4, c_l, hr_l, hc_l, hc_l11, hr4_0, hr4_2, hr4_4, hr4_5, h24_hp_le, hm4_l, hsteps4_l,
      h4_nf, h4_out, h4_lct⟩
  have h4_arena : arenaHi ≤ st4.mem (nodesBase - 1) := le_trans h4_lct.2.1 h4_lct.2.2.1
  have hx_ne_l : x ≠ l₁.rootId := nodeId_ne_rootId_of_not_mem hx1 hx_l
  have h4_x : ∀ off < NODE_STRIDE,
      nodeField st4.mem nodesBase x off = nodeField st2.mem nodesBase x off := fun off hoff =>
    nodeField_eq_of_outside_slot_lt_hp hx2 hx_ne_l hoff (by rw [h2_hp]; exact harena) hnb h4_out
  have h4_r_fields : ∀ u ∈ r₁.toList, ∀ off < NODE_STRIDE,
      nodeField st4.mem nodesBase u off = nodeField st2.mem nodesBase u off := fun u hu off hoff => by
    rcases hr_m.nodup_perm_mem hu with ⟨hu1, hu2⟩
    exact nodeField_eq_of_outside_slot_lt_hp hu2 (nodeId_ne_rootId_of_not_mem hu1 (fun h => hdisj h hu))
      hoff (by rw [h2_hp]; exact harena) hnb h4_out
  have h4_heap_lt : ∀ a, arenaHi ≤ a → a < st2.mem (nodesBase - 1) → st4.mem a = st2.mem a :=
    fun a ha1 ha2 => h4_lct.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)
  have h4_mr : TreeMemMatch w h L st4.mem nodesBase cap r₁ x 0 :=
    memAgree_treeMemMatch_of_nodeList h2_mr h4_r_fields h24_hp_le h4_heap_lt
  have h4_L : st4.mem (nodesBase - 3) = L := by
    have hlt3 : nodesBase - 3 < nodesBase + NODE_STRIDE := by unfold NODE_STRIDE; omega
    have hne3 : nodesBase - 3 ≠ nodesBase - 1 := by omega
    exact (h4_lct.2.2.2.2.2 (nodesBase - 3) (Or.inl ⟨hlt3, hne3⟩)).trans h2_L
  have h4_tp_ok : NumPtrOk st4.mem arenaHi (st4.mem (nodesBase - 1)) h L tPtr :=
    numPtrOk_congr h24_hp_le h4_heap_lt h2_tp_ok
  have h4_dmod : d % (capacity h L : ℤ) =
      (if tNeg = 0 then intVal st4.mem tPtr h L else -intVal st4.mem tPtr h L) % (capacity h L : ℤ) := by
    rw [intVal_agree_heap h4_heap_lt h2_tp_ok.2.1 h2_tp_ok.2.2.1]; exact h2_dmod
  have h4_fit_r : StepsShiftFit h L (evalMemSteps st4.mem nodesBase h L r₁ false 0) d := by
    rw [evalMemSteps_agree h2_mr h4_r_fields h4_heap_lt, evalMemSteps_agree hr_m h2_r_fields h2_heap_lt]
    exact hfit_r
  have h4_R_eq : nodeField st4.mem nodesBase x OFF_RIGHT = r₁.rootId :=
    (h4_x OFF_RIGHT (by decide)).trans
      ((h2_other OFF_RIGHT (by decide) (by decide) (by decide) (by decide)).trans hR)
  have h4_hp_lt : st4.mem (nodesBase - 1) + K_APPLY_TAG L < 2 ^ w := by
    rw [h2_hp] at hc_l
    omega
  -- 3. applyTag on r₁
  rcases applyTagChild_exec hp_ok hbase hnb hx2 (by decide) st4 h4_L h4_arena
      h4_lct.2.2.2.2.1 h4_hp_lt (memAgree_slotZero_of_lctFrame (by omega) h2_0 h4_lct)
      hr4_0 hr4_2 hr4_4 hr4_5 h4_R_eq h4_mr hr_nd htn_le h4_tp_ok h4_dmod h4_fit_r ω with
    ⟨st6, c_r, hr_r, hc_r, _hc_r11, _, _, _, _, h46_hp_le, hm6_r, hsteps6_r, h6_nf, h6_out, h6_lct⟩
  have hrun : Runs w p ω
      (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
       Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
       Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
       Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
       Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0) ;;
       Stmt.assign 6 (fieldLoadExpr 2 OFF_LEFT) ;;
       Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5] ;;
       Stmt.assign 6 (fieldLoadExpr 2 OFF_RIGHT) ;;
       Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5])
      st1 .normal st6 (c_clr + (c_l + c_r + 1) + 1) :=
    runs_seq5_normal hr_clr (runs_seq2_normal hr_l hr_r)
  have hx_ne_r : x ≠ r₁.rootId := nodeId_ne_rootId_of_not_mem hx1 hx_r
  have h6_x : ∀ off < NODE_STRIDE,
      nodeField st6.mem nodesBase x off = nodeField st4.mem nodesBase x off := fun off hoff =>
    nodeField_eq_of_outside_slot_lt_hp hx2 hx_ne_r hoff h4_arena hnb h6_out
  have h6_l_fields : ∀ u ∈ l₁.toList, ∀ off < NODE_STRIDE,
      nodeField st6.mem nodesBase u off = nodeField st4.mem nodesBase u off := fun u hu off hoff => by
    rcases hl_m.nodup_perm_mem hu with ⟨hu1, hu2⟩
    exact nodeField_eq_of_outside_slot_lt_hp hu2 (nodeId_ne_rootId_of_not_mem hu1 (fun h => hdisj hu h))
      hoff h4_arena hnb h6_out
  have h6_heap4 : ∀ a, arenaHi ≤ a → a < st4.mem (nodesBase - 1) → st6.mem a = st4.mem a :=
    fun a ha1 ha2 => h6_lct.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)
  have hm6_l : TreeMemMatch w h L st6.mem nodesBase cap l₁ x 0 :=
    memAgree_treeMemMatch_of_nodeList hm4_l h6_l_fields h46_hp_le h6_heap4
  have h16_lct : LctFrame (nodesBase + NODE_STRIDE) arenaHi (nodesBase - 1) st1.mem st6.mem :=
    lctFrame_trans h2_lct (lctFrame_trans h4_lct h6_lct)
  have h6_heap_lt : ∀ a, arenaHi ≤ a → a < st1.mem (nodesBase - 1) → st6.mem a = st1.mem a :=
    fun a ha1 ha2 => h16_lct.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)
  have hsteps6_l : evalMemSteps st6.mem nodesBase h L l₁ false 0 =
      (evalMemSteps st1.mem nodesBase h L l₁ false 0).map (fun q => q.addDelta d) := by
    rw [evalMemSteps_agree hm4_l h6_l_fields h6_heap4, hsteps4_l,
      evalMemSteps_agree hl_m h2_l_fields h2_heap_lt]
  have hsteps6_r' : evalMemSteps st6.mem nodesBase h L r₁ false 0 =
      (evalMemSteps st1.mem nodesBase h L r₁ false 0).map (fun q => q.addDelta d) := by
    rw [hsteps6_r, evalMemSteps_agree h2_mr h4_r_fields h4_heap_lt,
      evalMemSteps_agree hr_m h2_r_fields h2_heap_lt]
  have h6_x_ht : nodeField st6.mem nodesBase x OFF_HAS_TAG = 0 :=
    (h6_x OFF_HAS_TAG (by decide)).trans ((h4_x OFF_HAS_TAG (by decide)).trans h2_ht)
  have h6_x_tp : nodeField st6.mem nodesBase x OFF_TAG_PTR = 0 :=
    (h6_x OFF_TAG_PTR (by decide)).trans ((h4_x OFF_TAG_PTR (by decide)).trans h2_tp)
  have h6_x_tn : nodeField st6.mem nodesBase x OFF_TAG_NEG = 0 :=
    (h6_x OFF_TAG_NEG (by decide)).trans ((h4_x OFF_TAG_NEG (by decide)).trans h2_tn)
  have h6_x_other : ∀ off < NODE_STRIDE, off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      nodeField st6.mem nodesBase x off = nodeField st1.mem nodesBase x off :=
    fun off hoff h1 h2 h3 => (h6_x off hoff).trans ((h4_x off hoff).trans (h2_other off hoff h1 h2 h3))
  have h6_unmod : ∀ u ≤ cap, ∀ off < NODE_STRIDE,
      off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
      off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      nodeField st6.mem nodesBase u off = nodeField st1.mem nodesBase u off := by
    intro u huc off hlo h1 h2 h3 h4 h5 h6 h7 h8
    have h64 := h6_nf u huc off hlo h1 h2 h3 h4 h5 h6 h7 h8
    have h42 := h4_nf u huc off hlo h1 h2 h3 h4 h5 h6 h7 h8
    have h21 : nodeField st2.mem nodesBase u off = nodeField st1.mem nodesBase u off := by
      by_cases hux : u = x
      · subst hux; exact h2_other off hlo h6 h7 h8
      · exact h2_node hux off hlo
    exact h64.trans (h42.trans h21)
  have hisv6 : ∀ u ∈ (AuxTree.node x l₁ r₁).toList,
      nodeField st6.mem nodesBase u OFF_ISV = nodeField st1.mem nodesBase u OFF_ISV := fun u hu =>
    h6_unmod u (htx.nodup_perm_mem hu).2 OFF_ISV (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrev6 : ∀ u ∈ (AuxTree.node x l₁ r₁).toList,
      nodeField st6.mem nodesBase u OFF_REV = nodeField st1.mem nodesBase u OFF_REV := fun u hu =>
    h6_unmod u (htx.nodup_perm_mem hu).2 OFF_REV (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases pushDownPhase2_post htx hrev1 hdmod hfit_l hfit_r hm6_l hm6_r
      hsteps6_l hsteps6_r' h6_x_ht h6_x_tp h6_x_tn h6_x_other hisv6 hrev6 h16_lct.2.2.1 h6_heap_lt with
    ⟨hm_post, hsteps_post, heval_post⟩
  have hcost_bound : c_clr + (c_l + c_r + 1) + 1 + (st6.mem (nodesBase - 1) - st1.mem (nodesBase - 1)) ≤
      2 * K_APPLY_TAG L + 60 := by
    have hp12 : st1.mem (nodesBase - 1) ≤ st4.mem (nodesBase - 1) := by rw [← h2_hp]; exact h24_hp_le
    have hp46 : st4.mem (nodesBase - 1) ≤ st6.mem (nodesBase - 1) := h46_hp_le
    rw [h2_hp] at hc_l
    omega
  refine ⟨st6, _, hrun, hcost_bound, h16_lct.2.2.1, hm_post, hsteps_post, heval_post, h6_x_ht, ?_,
    ?_, ?_, h16_lct⟩
  · simp only [revFlag, hrev6 x (by simp [AuxTree.toList])]; exact hrev1
  · intro u huc hu off hoff
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton, not_or] at hu
    rcases hu with ⟨⟨hu_l, hu_x⟩, hu_r⟩
    by_cases hu0 : u = 0
    · subst hu0
      have hlt : nodesBase + NODE_STRIDE * 0 + off < nodesBase + NODE_STRIDE := by
        unfold NODE_STRIDE at hoff ⊢; omega
      have hne_hdr : nodesBase + NODE_STRIDE * 0 + off ≠ nodesBase - 1 := by omega
      exact h16_lct.2.2.2.2.2 _ (Or.inl ⟨hlt, hne_hdr⟩)
    · have hu_pos : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu0
      have h64 : nodeField st6.mem nodesBase u off = nodeField st4.mem nodesBase u off :=
        nodeField_eq_of_outside_slot_lt_hp huc (nodeId_ne_rootId_of_not_mem hu_pos hu_r)
          hoff h4_arena hnb h6_out
      have h42 : nodeField st4.mem nodesBase u off = nodeField st2.mem nodesBase u off :=
        nodeField_eq_of_outside_slot_lt_hp huc (nodeId_ne_rootId_of_not_mem hu_pos hu_l)
          hoff (by rw [h2_hp]; exact harena) hnb h4_out
      exact h64.trans (h42.trans (h2_node hu_x off hoff))
  · intro u huc off hoff
    rcases isStaticPayloadOff_ne_struct hoff with
      ⟨hlo, _, _, _, _, _, _, _, hfl, haf, hab, _, _, _, _, hht, htp, htn, _, hm1v, _, _, _, hm2v, _, _⟩
    exact h6_unmod u huc off hlo haf hab hfl hm1v hm2v hht htp htn

private theorem pushDownBody_afterPhase1 {w h L nodesBase cap x parId pp : ℕ}
    {p : Program} {sp : SplayProcs} {mem₁ : ℕ → ℕ}
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : mem₁ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₁ (nodesBase - 1))
    (hz : ZeroFrom mem₁ (mem₁ (nodesBase - 1)))
    (hhp_lt : mem₁ (nodesBase - 1) + 2 * K_APPLY_TAG L < 2 ^ w)
    (h0 : SlotZeroOk mem₁ nodesBase)
    (st1 : State)
    (hmem1 : st1.mem = mem₁)
    (hr0 : st1.regs 0 = nodesBase)
    (hr2 : st1.regs 2 = nodesBase + NODE_STRIDE * x)
    {l₁ r₁ : AuxTree} (ht : TreeMemMatch w h L mem₁ nodesBase cap (.node x l₁ r₁) parId pp)
    (hnd : (AuxTree.node x l₁ r₁).toList.Nodup)
    (hrev1 : revFlag mem₁ nodesBase x = false) :
    ∀ ω, ∃ st' c,
      Runs w p ω
        (Stmt.assign 3 (fieldLoadExpr 2 OFF_HAS_TAG) ;;
         Stmt.cond (.reg 3)
           (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
            Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
            Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
            Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
            Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0) ;;
            Stmt.assign 6 (fieldLoadExpr 2 OFF_LEFT) ;;
            Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5] ;;
            Stmt.assign 6 (fieldLoadExpr 2 OFF_RIGHT) ;;
            Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5])
           Stmt.nop ;;
         Stmt.ret (.const 0))
        st1 (.returned 0) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₁ (nodesBase - 1)) ≤ 2 * K_APPLY_TAG L + 80 ∧
      mem₁ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap (.node x l₁ r₁) parId pp ∧
      evalMemSteps st'.mem nodesBase h L (.node x l₁ r₁) false 0 =
        evalMemSteps mem₁ nodesBase h L (.node x l₁ r₁) false 0 ∧
      (AuxTree.node x l₁ r₁).evalInorder (revFlag st'.mem nodesBase) false =
        (AuxTree.node x l₁ r₁).evalInorder (revFlag mem₁ nodesBase) false ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      revFlag st'.mem nodesBase x = false ∧
      (∀ u ≤ cap, u ∉ (AuxTree.node x l₁ r₁).toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₁ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₁ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₁ st'.mem := by
  subst hmem1
  intro ω
  have htx := ht
  rcases ht with ⟨_, hx2, _⟩
  have hw0 : (0 : ℕ) < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  let htag := nodeField st1.mem nodesBase x OFF_HAS_TAG
  let st_ld : State := { mem := st1.mem, regs := Function.update st1.regs 3 htag, pos := st1.pos }
  have hrld_0 : st_ld.regs 0 = nodesBase := by dsimp [st_ld]; rw [Function.update_of_ne (by decide)]; exact hr0
  have hrld_2 : st_ld.regs 2 = nodesBase + NODE_STRIDE * x := by
    dsimp [st_ld]; rw [Function.update_of_ne (by decide)]; exact hr2
  have hrld_3 : st_ld.regs 3 = htag := by dsimp [st_ld]; exact Function.update_self _ _ _
  have hr_ld : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_HAS_TAG)) st1 .normal st_ld 5 :=
    runs_assign_iff.mpr ⟨htag, by simpa [nodeField, htag] using eval_fieldLoadExpr hr2 (nodeAddr_lt_pow hbase hx2 (by decide)), rfl, rfl, rfl⟩
  by_cases hhtz : htag = 0
  · have hcond : Runs w p ω
        (Stmt.cond (.reg 3)
          (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
           Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
           Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
           Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
           Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0) ;;
           Stmt.assign 6 (fieldLoadExpr 2 OFF_LEFT) ;;
           Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5] ;;
           Stmt.assign 6 (fieldLoadExpr 2 OFF_RIGHT) ;;
           Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5])
          Stmt.nop)
        st_ld .normal st_ld 3 :=
      runs_cond_iff.mpr ⟨htag, 1, Expr.eval_reg_of_eq hrld_3,
        by simp only [hhtz, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    have hret : Runs w p ω (Stmt.ret (.const 0)) st_ld (.returned 0) st_ld 2 :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩
    have hrun := runs_seq_iff.mpr (Or.inr ⟨st_ld, _, _, hr_ld,
      runs_seq_iff.mpr (Or.inr ⟨st_ld, _, _, hcond, hret, rfl⟩), rfl⟩)
    have hstld_mem : st_ld.mem = st1.mem := rfl
    exact ⟨st_ld, _, hrun, by rw [hstld_mem, Nat.sub_self]; omega, le_rfl, htx, rfl, rfl, hhtz, hrev1,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
      lctFrame_refl (by unfold NODE_STRIDE; omega) harena hz⟩
  · rcases pushDownTagBranch_runs hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 st_ld rfl
        hrld_0 hrld_2 htx hnd hrev1 hhtz ω with
      ⟨st_br, c_br, hr_br, hc_br, hhp_le, hm_br, hsteps_br, heval_br, hht_br, hrev_br,
        hout_br, hstat_br, hlct_br⟩
    have hcond : Runs w p ω
        (Stmt.cond (.reg 3)
          (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
           Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
           Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
           Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
           Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0) ;;
           Stmt.assign 6 (fieldLoadExpr 2 OFF_LEFT) ;;
           Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5] ;;
           Stmt.assign 6 (fieldLoadExpr 2 OFF_RIGHT) ;;
           Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5])
          Stmt.nop)
        st_ld .normal st_br (1 + c_br + 1) :=
      runs_cond_iff.mpr ⟨htag, c_br, Expr.eval_reg_of_eq hrld_3,
        by simpa [hhtz] using hr_br, rfl⟩
    have hret : Runs w p ω (Stmt.ret (.const 0)) st_br (.returned 0) st_br 2 :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const hw0, rfl, rfl, rfl⟩
    have hrun := runs_seq_iff.mpr (Or.inr ⟨st_ld, _, _, hr_ld,
      runs_seq_iff.mpr (Or.inr ⟨st_br, _, _, hcond, hret, rfl⟩), rfl⟩)
    exact ⟨st_br, _, hrun, by omega, hhp_le, hm_br, hsteps_br, heval_br, hht_br, hrev_br,
      hout_br, hstat_br, hlct_br⟩

/-! ### Top-level subtree and ambient-tree `pushDownBody` specifications -/

theorem pushDownBody_runs_subtree {w h L nodesBase cap x parId pp : ℕ}
    {p : Program} {sp : SplayProcs} {mem₀ : ℕ → ℕ} (pos : ℕ)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + K_PUSH_DOWN L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {l r : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap (.node x l r) parId pp)
    (hnd : (AuxTree.node x l r).toList.Nodup) :
    ∀ ω, ∃ st' c,
      let s' := if nodeField mem₀ nodesBase x OFF_REV = 0
        then AuxTree.node x l r
        else (AuxTree.node x l r).pushDownRoot
      Runs w p ω (pushDownBody sp) (startState [nodesBase, x] mem₀ pos) (.returned 0) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_PUSH_DOWN L ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap s' parId pp ∧
      evalMemSteps st'.mem nodesBase h L s' false 0 =
        evalMemSteps mem₀ nodesBase h L (.node x l r) false 0 ∧
      s'.evalInorder (revFlag st'.mem nodesBase) false =
        (AuxTree.node x l r).evalInorder (revFlag mem₀ nodesBase) false ∧
      revFlag st'.mem nodesBase x = false ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      (∀ u ≤ cap, u ∉ (AuxTree.node x l r).toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  intro ω
  have htx := ht
  rcases ht with ⟨hx1, hx2, _⟩
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  let st0 := startState [nodesBase, x] mem₀ pos
  have hr0_0 : st0.regs 0 = nodesBase := rfl
  have hr0_1 : st0.regs 1 = x := rfl
  let ptr := nodesBase + NODE_STRIDE * x
  let st_ptr : State := { mem := mem₀, regs := Function.update st0.regs 2 ptr, pos := st0.pos }
  have hp_lt_pow : ptr < 2 ^ w := nodePtr_lt_pow hbase hx2
  have ha_ptr : Runs w p ω (Stmt.assign 2 (nodePtrExpr 0 1)) st0 .normal st_ptr 6 :=
    runs_assign_iff.mpr ⟨ptr, eval_nodePtrExpr hstride hr0_0 hr0_1 hp_lt_pow, rfl, rfl, rfl⟩
  have hrp_0 : st_ptr.regs 0 = nodesBase := by dsimp [st_ptr]; rw [Function.update_of_ne (by decide)]; exact hr0_0
  have hrp_2 : st_ptr.regs 2 = ptr := by dsimp [st_ptr]; exact Function.update_self _ _ _
  let rflag := nodeField mem₀ nodesBase x OFF_REV
  let st_rv : State := { mem := mem₀, regs := Function.update st_ptr.regs 3 rflag, pos := st_ptr.pos }
  have ha_rv : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_REV)) st_ptr .normal st_rv 5 :=
    runs_assign_iff.mpr ⟨rflag, by simpa [st_ptr, ptr, nodeField, rflag] using eval_fieldLoadExpr hrp_2 (nodeAddr_lt_pow hbase hx2 (by decide)), rfl, rfl, rfl⟩
  have hrv_0 : st_rv.regs 0 = nodesBase := by dsimp [st_rv]; rw [Function.update_of_ne (by decide)]; exact hrp_0
  have hrv_2 : st_rv.regs 2 = ptr := by dsimp [st_rv]; rw [Function.update_of_ne (by decide)]; exact hrp_2
  have hrv_3 : st_rv.regs 3 = rflag := by dsimp [st_rv]; exact Function.update_self _ _ _
  have hrv_mem : st_rv.mem = mem₀ := rfl
  have hhp_tag_lt : mem₀ (nodesBase - 1) + 2 * K_APPLY_TAG L < 2 ^ w :=
    pushDown_tag_heap_lt hhp_lt
  by_cases hrevz : rflag = 0
  · have hrev0 : revFlag mem₀ nodesBase x = false := by
      simp [revFlag, show nodeField mem₀ nodesBase x OFF_REV = 0 from hrevz]
    have hcond_rv : Runs w p ω
        (Stmt.cond (.reg 3)
          (Stmt.assign 4 (fieldLoadExpr 2 OFF_LEFT) ;;
           Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
           Stmt.assign 4 (fieldLoadExpr 2 OFF_RIGHT) ;;
           Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
           Stmt.store (fieldAddrExpr 2 OFF_REV) (.const 0))
          Stmt.nop)
        st_rv .normal st_rv 3 :=
      runs_cond_iff.mpr ⟨rflag, 1, Expr.eval_reg_of_eq hrv_3,
        by simp only [hrevz, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    rcases pushDownBody_afterPhase1 hp_ok hbase hnb hL_hdr harena hz hhp_tag_lt
        h0 st_rv hrv_mem hrv_0 hrv_2 htx hnd hrev0 ω with
      ⟨st', c_p2, hr_p2, hc_p2, hhp_le, hm', hsteps', heval', hht', hrev', hout', hstat', hlct'⟩
    have hbody : Runs w p ω
        (Stmt.assign 2 (nodePtrExpr 0 1) ;;
         Stmt.assign 3 (fieldLoadExpr 2 OFF_REV) ;;
         Stmt.cond (.reg 3) _ Stmt.nop ;;
         _)
        st0 (.returned 0) st' (6 + (5 + (3 + c_p2 + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st_ptr, _, _, ha_ptr,
        runs_seq_iff.mpr (Or.inr ⟨st_rv, _, _, ha_rv,
          runs_seq_iff.mpr (Or.inr ⟨st_rv, _, _, hcond_rv, hr_p2, rfl⟩), rfl⟩), rfl⟩)
    have hx_ne : x ≠ 0 := by omega
    have hfull : Runs w p ω (pushDownBody sp) st0 (.returned 0) st'
        (1 + (6 + (5 + (3 + c_p2 + 1) + 1) + 1) + 1) :=
      runs_cond_iff.mpr ⟨x, _, Expr.eval_reg_of_eq hr0_1, by simpa [pushDownBody, hx_ne] using hbody, rfl⟩
    dsimp only
    simp only [show nodeField mem₀ nodesBase x OFF_REV = 0 from hrevz, ↓reduceIte]
    exact ⟨st', _, hfull, pushDown_norev_cost_lt hc_p2, hhp_le, hm', hsteps', heval',
      hrev', hht', hout', hstat', hlct'⟩
  · rcases pushDownRevBranch_runs hp_ok hbase st_rv hrv_mem hrv_0 hrv_2 htx hnd hrevz ω with
      ⟨st1, c_p1, hr_p1, hc_p1, hr1_0, hr1_2, h1_hp, hm1, hsteps1, heval1, hrev1,
        hout1, hstat1, hpres1⟩
    have hlct01 : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st1.mem :=
      lctFrame_of_memPreservedOutside hpres1 (by unfold NODE_STRIDE; omega) harena hz
    have h1_L : st1.mem (nodesBase - 3) = L := by
      have hlt3 : nodesBase - 3 < nodesBase + NODE_STRIDE := by unfold NODE_STRIDE; omega
      have hne3 : nodesBase - 3 ≠ nodesBase - 1 := by omega
      exact (hlct01.2.2.2.2.2 (nodesBase - 3) (Or.inl ⟨hlt3, hne3⟩)).trans hL_hdr
    have h1_nd : (AuxTree.node x l.revRoot r.revRoot).toList.Nodup :=
      (AuxTree.pushDownRoot_toList_perm (.node x l r)).symm.nodup_iff.mp hnd
    have h1_hp_lt : st1.mem (nodesBase - 1) + 2 * K_APPLY_TAG L < 2 ^ w := by
      rw [h1_hp]; exact hhp_tag_lt
    rcases pushDownBody_afterPhase1 hp_ok hbase hnb h1_L (le_trans hlct01.2.1 hlct01.2.2.1) hlct01.2.2.2.2.1
        h1_hp_lt (memAgree_slotZero_of_lctFrame (by omega) h0 hlct01) st1 rfl hr1_0 hr1_2
        hm1 h1_nd hrev1 ω with
      ⟨st', c_p2, hr_p2, hc_p2, hhp12, hm', hsteps2, heval2, hht', hrev', hout2, hstat2, hlct12⟩
    have hcond_rv : Runs w p ω
        (Stmt.cond (.reg 3)
          (Stmt.assign 4 (fieldLoadExpr 2 OFF_LEFT) ;;
           Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
           Stmt.assign 4 (fieldLoadExpr 2 OFF_RIGHT) ;;
           Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
           Stmt.store (fieldAddrExpr 2 OFF_REV) (.const 0))
          Stmt.nop)
        st_rv .normal st1 (1 + c_p1 + 1) :=
      runs_cond_iff.mpr ⟨rflag, c_p1, Expr.eval_reg_of_eq hrv_3, by simpa [hrevz] using hr_p1, rfl⟩
    have hbody : Runs w p ω
        (Stmt.assign 2 (nodePtrExpr 0 1) ;;
         Stmt.assign 3 (fieldLoadExpr 2 OFF_REV) ;;
         Stmt.cond (.reg 3) _ Stmt.nop ;;
         _)
        st0 (.returned 0) st' (6 + (5 + ((1 + c_p1 + 1) + c_p2 + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st_ptr, _, _, ha_ptr,
        runs_seq_iff.mpr (Or.inr ⟨st_rv, _, _, ha_rv,
          runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hcond_rv, hr_p2, rfl⟩), rfl⟩), rfl⟩)
    have hx_ne : x ≠ 0 := by omega
    have hfull : Runs w p ω (pushDownBody sp) st0 (.returned 0) st'
        (1 + (6 + (5 + ((1 + c_p1 + 1) + c_p2 + 1) + 1) + 1) + 1) :=
      runs_cond_iff.mpr ⟨x, _, Expr.eval_reg_of_eq hr0_1, by simpa [pushDownBody, hx_ne] using hbody, rfl⟩
    dsimp only
    simp only [show nodeField mem₀ nodesBase x OFF_REV ≠ 0 from hrevz, ↓reduceIte]
    have hperm_lr : ∀ u, u ∉ (AuxTree.node x l r).toList → u ∉ (AuxTree.node x l.revRoot r.revRoot).toList :=
      fun u hu hin => hu ((AuxTree.pushDownRoot_toList_perm (.node x l r)).mem_iff.1 hin)
    have hhp_final : mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) := by rw [← h1_hp]; exact hhp12
    have hcb : 1 + (6 + (5 + ((1 + c_p1 + 1) + c_p2 + 1) + 1) + 1) + 1 +
        (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_PUSH_DOWN L := by
      rw [← h1_hp]
      exact pushDown_total_cost_lt hc_p1 hc_p2
    refine ⟨st', _, hfull, hcb, hhp_final, hm', hsteps2.trans hsteps1, heval2.trans heval1,
      hrev', hht', ?_, ?_, lctFrame_trans hlct01 hlct12⟩
    · intro u huc hu off hoff
      exact (hout2 u huc (hperm_lr u hu) off hoff).trans (hout1 u huc hu off hoff)
    · intro u huc off hoff
      exact (hstat2 u huc off hoff).trans (hstat1 u huc off hoff)

theorem pushDownBody_runs_in_tree {w h L nodesBase cap x parId pp : ℕ}
    {p : Program} {sp : SplayProcs} {mem₀ : ℕ → ℕ} (pos : ℕ)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + K_PUSH_DOWN L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap t parId pp)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) :
    ∀ ω, ∃ st' c t',
      Runs w p ω (pushDownBody sp) (startState [nodesBase, x] mem₀ pos) (.returned 0) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_PUSH_DOWN L ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap t' parId pp ∧
      t'.toList.Perm t.toList ∧
      t'.rootId = t.rootId ∧
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧ t'.treePhi vSize = t.treePhi vSize) ∧
      (∀ u, t'.depthOf u = t.depthOf u ∧ t'.pathTo u = t.pathTo u) ∧
      revFlag st'.mem nodesBase x = false ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      (∀ u ≤ cap, u ∉ (t.findSubtree x).toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  intro ω
  have hfm := AuxTree.findSubtree_match ht hx
  rcases AuxTree.findSubtree_mem_toList hx with ⟨hne, hroot⟩
  have hnd_sub : (t.findSubtree x).toList.Nodup := by
    clear ht hfm hne hroot
    induction t with
    | leaf => simp [AuxTree.toList] at hx
    | node id l r ihl ihr =>
        have hnd' := hnd
        simp only [AuxTree.toList, List.nodup_append, List.nodup_cons] at hnd'
        rcases hnd' with ⟨⟨hl_nd, _⟩, hr_nd, _⟩
        simp only [AuxTree.findSubtree]
        split_ifs with h1 h2
        · exact hnd
        · exact ihl hl_nd h2
        · have hr : x ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (hl | rfl) | hr
            · exact absurd hl h2
            · exact absurd rfl h1
            · exact hr
          exact ihr hr_nd hr
  cases hfind : t.findSubtree x with
  | leaf => contradiction
  | node y l r =>
      rw [hfind] at hne hroot hfm hnd_sub
      dsimp only [AuxTree.rootId] at hroot
      subst hroot
      rcases pushDownBody_runs_subtree pos hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 hfm hnd_sub ω with
        ⟨st', c, hr_sub, hc, hhp_le, hs_match, hs_steps, hs_eval, hrev_x, hht_x, hout, hstat, hlct⟩
      let s' := if nodeField mem₀ nodesBase y OFF_REV = 0
        then AuxTree.node y l r
        else (AuxTree.node y l r).pushDownRoot
      have hs_ne : s' ≠ .leaf := by
        dsimp only [s']; split_ifs <;> simp [AuxTree.pushDownRoot]
      have hs_root : s'.rootId = y := by
        dsimp only [s']; split_ifs <;> simp [AuxTree.pushDownRoot, AuxTree.rootId]
      have hs_perm : s'.toList.Perm (t.findSubtree y).toList := by
        rw [hfind]; dsimp only [s']
        split_ifs
        · exact List.Perm.refl _
        · exact AuxTree.pushDownRoot_toList_perm _
      have hs_eval' : s'.evalInorder (revFlag st'.mem nodesBase) false =
          (t.findSubtree y).evalInorder (revFlag mem₀ nodesBase) false := by
        rw [hfind]; exact hs_eval
      have hs_vcnt : listVcnt st'.mem nodesBase (s'.evalInorder (revFlag st'.mem nodesBase) false) =
          listVcnt mem₀ nodesBase ((t.findSubtree y).evalInorder (revFlag mem₀ nodesBase) false) := by
        rw [hs_eval']
        apply listVcnt_agree_of_mem
        intro u hu
        have hu_sub : u ∈ (t.findSubtree y).toList :=
          (AuxTree.evalInorder_perm _ _ _).mem_iff.1 hu
        have hu_t : u ∈ t.toList := AuxTree.findSubtree_subset hu_sub
        exact hstat u (ht.nodup_perm_mem hu_t).2 OFF_ISV (by simp [IsStaticPayloadOff])
      have hs_steps' : evalMemSteps st'.mem nodesBase h L s' false 0 =
          evalMemSteps mem₀ nodesBase h L (t.findSubtree y) false 0 := by
        rw [hfind]; exact hs_steps
      have hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
          st'.mem a = mem₀ a :=
        fun a ha1 ha2 => hlct.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)
      have houter : ∀ u ∈ t.toList, u ∉ (t.findSubtree y).toList →
          ∀ off < NODE_STRIDE, nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off := by
        intro u hu_t hu_nin off hoff
        rw [hfind] at hu_nin
        exact hout u (ht.nodup_perm_mem hu_t).2 hu_nin off hoff
      have hrep := AuxTree.replaceSubtree_preserves ht hnd hx hs_match hs_ne hs_perm
        hs_eval' hs_vcnt hs_steps' hhp_le hheap
        (fun u hu_t hu_nin off hoff _ _ => houter u hu_t hu_nin off hoff)
        (fun u hu_t hu_nin => by
          rw [houter u hu_t hu_nin OFF_LEFT (by decide), hs_root]
          split_ifs with heq <;> [exact heq; rfl])
        (fun u hu_t hu_nin => by
          rw [houter u hu_t hu_nin OFF_RIGHT (by decide), hs_root]
          split_ifs with heq <;> [exact heq; rfl])
      rcases hrep with ⟨hm_t', hperm_t', heval_t', _, hsteps_t'⟩
      refine ⟨st', c, t.replaceSubtree y s', hr_sub, hc, hhp_le, hm_t', hperm_t', ?_,
        heval_t', hsteps_t', ?_, ?_, hrev_x, hht_x, hout, hstat, hlct⟩
      · have ht_ne : t ≠ .leaf := by cases t with | leaf => simp [AuxTree.toList] at hx | node _ _ _ => simp
        rw [AuxTree.replaceSubtree_rootId ht_ne hs_ne, hs_root]
        split_ifs with heq <;> [exact heq.symm; rfl]
      · intro vSize
        have hsp_sz : s'.treeSize vSize = (t.findSubtree y).treeSize vSize := by
          rw [hfind]; dsimp only [s']; split_ifs <;> simp [AuxTree.pushDownRoot_treeSize]
        have hsp_phi : s'.treePhi vSize = (t.findSubtree y).treePhi vSize := by
          rw [hfind]; dsimp only [s']; split_ifs <;> simp [AuxTree.pushDownRoot_treePhi]
        exact AuxTree.replaceSubtree_treeSize_treePhi vSize hnd hx hsp_sz hsp_phi
      · intro u
        have hdp : ∀ z, s'.depthOf z = (t.findSubtree y).depthOf z ∧
            s'.pathTo z = (t.findSubtree y).pathTo z := by
          intro z
          rw [hfind]; dsimp only [s']; split_ifs
          · exact ⟨rfl, rfl⟩
          · exact AuxTree.pushDownRoot_depth_path hnd_sub z
        exact AuxTree.replaceSubtree_depth_path hnd hx hs_perm hdp

end

end MinCostFlow.LinkCut.Prog
