module

public import MinCostFlow.LinkCut.Prog.MathForestExposePure

/-!
# Expose Safety Helpers, Tree Reparenting, and Frame Preservation

Provides arithmetic headroom bounds (`M_EXPOSE`), `SafeMem` updates for structural pointer
writes, `evalMemSteps` agreement under reparenting / non-aggregate updates, `SplayForestOk`
preservation under `detach` and `splice`, and `PullPre` construction lemmas.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section ArithAndDepthBounds

/-- Constant absorbing one light splice iteration (`splay` + `pull` + new heavy dashed edge). -/
def M_EXPOSE (L : ℕ) : ℕ :=
  C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 200

theorem expose_heavy_cancel_le (L : ℕ) :
    C_SPLAY_CONST L + K_PULL L + 160 ≤ C_HEAVY L := by
  unfold C_HEAVY
  omega

theorem expose_light_le_M (L : ℕ) :
    C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 160 ≤ M_EXPOSE L := by
  unfold M_EXPOSE
  omega

theorem expose_total_budget_le (L n : ℕ) :
    (9 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) +
      M_EXPOSE L + C_SPLAY_CONST L + C_HEAVY L + 200 ≤
      C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) := by
  have hk : K_SPLAY_STEP L = 7600 * (L + 1) + 1540 := by
    unfold K_SPLAY_STEP K_DOUBLE K_ROTATE K_PULL K_PUSH_PATH K_PUSH_DOWN
    ring
  have hch : C_HEAVY L ≤ 8200 * (L + 1) := c_heavy_le L
  have hm : M_EXPOSE L ≤ 16000 * (L + 1) := by
    unfold M_EXPOSE C_SPLAY_CONST K_PULL
    omega
  have hlog : 1 ≤ Nat.log 2 (n + 2) + 1 := Nat.succ_pos _
  have h1 : 9 * K_SPLAY_STEP L + M_EXPOSE L ≤ 100000 * (L + 1) := by omega
  have h2 : M_EXPOSE L + C_SPLAY_CONST L + C_HEAVY L + 200 ≤ 40000 * (L + 1) := by
    unfold C_SPLAY_CONST; omega
  have h3 : (M_EXPOSE L + C_SPLAY_CONST L + C_HEAVY L + 200) * 1 ≤
      40000 * (L + 1) * (Nat.log 2 (n + 2) + 1) := by nlinarith
  have h4 : (9 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) ≤
      100000 * (L + 1) * (Nat.log 2 (n + 2) + 1) := Nat.mul_le_mul_right _ h1
  unfold C_EXPOSE_OP
  nlinarith

theorem auxTree_depthOf_lt_length {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    t.depthOf x < t.toList.length := by
  induction t with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton, List.length_append,
        List.length_singleton] at hx ⊢
      simp only [AuxTree.depthOf]
      split_ifs with h1 h2 h3
      · omega
      · have := ihl h2; omega
      · have := ihr h3; omega
      · rcases hx with (hl | rfl) | hr
        · exact absurd hl h2
        · exact absurd rfl h1
        · exact absurd hr h3

theorem splayForestOk_toList_length_le {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees)
    {t : AuxTree} (ht : t ∈ trees) :
    t.toList.length ≤ cap := by
  have hsub : t.toList ⊆ (List.range cap).map (· + 1) := fun u hu =>
    hok.perm.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, hu⟩)
  have hnd_all : (trees.flatMap AuxTree.toList).Nodup :=
    hok.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hnd : t.toList.Nodup := list_nodup_of_flatMap_nodup hnd_all ht
  have hc := Finset.card_le_card
    (show t.toList.toFinset ⊆ ((List.range cap).map (· + 1)).toFinset from fun u hu => by
      simp only [List.mem_toFinset] at hu ⊢; exact hsub hu)
  rw [List.toFinset_card_of_nodup hnd] at hc
  exact le_trans hc (Nat.le_trans (List.toFinset_card_le _) (by simp))

theorem splay_headroom_le (L n d : ℕ) (hd : d < lctCap n) :
    K_PUSH_PATH L * (d + 1) + 8 * L * d + 4 * L ≤ 6000 * (L + 1) * (n + 2) := by
  have hcap : lctCap n = 2 * n := rfl
  have hpp : K_PUSH_PATH L = 2200 * (L + 1) + 120 := by
    unfold K_PUSH_PATH K_PUSH_DOWN; rfl
  have h1 : d + 1 ≤ 2 * (n + 1) := by omega
  have h2 : d ≤ 2 * (n + 1) := by omega
  nlinarith

theorem expose_enter_loop_budget_le (L n : ℕ) :
    3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L +
      K_PULL L + C_HEAVY L + 100 +
      (3 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) +
      6000 * (L + 1) * (n + 2) ≤
      C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) + 7000 * (L + 1) * (n + 2) := by
  have hk : K_SPLAY_STEP L = 7600 * (L + 1) + 1540 := by
    unfold K_SPLAY_STEP K_DOUBLE K_ROTATE K_PULL K_PUSH_PATH K_PUSH_DOWN; ring
  have hch : C_HEAVY L ≤ 8200 * (L + 1) := c_heavy_le L
  have hm : M_EXPOSE L ≤ 16000 * (L + 1) := by
    unfold M_EXPOSE C_SPLAY_CONST K_PULL; omega
  have hlog : 1 ≤ Nat.log 2 (n + 2) + 1 := Nat.succ_pos _
  have hc : C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 100 ≤ 16000 * (L + 1) := by
    unfold C_SPLAY_CONST K_PULL; omega
  have hlog_bd : (C_SPLAY_CONST L + K_PULL L + C_HEAVY L + 100) * 1 ≤
      16000 * (L + 1) * (Nat.log 2 (n + 2) + 1) := by nlinarith
  have h1 : 6 * K_SPLAY_STEP L + M_EXPOSE L ≤ 80000 * (L + 1) := by omega
  unfold C_EXPOSE_OP
  nlinarith

end ArithAndDepthBounds

section MemoryAndSafeHelpers

theorem ptrOffs_ne_struct {off : ℕ} (hoff : off ∈ ptrOffs) :
    off ≠ OFF_LEFT ∧ off ≠ OFF_RIGHT ∧ off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR := by
  simp only [ptrOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem SafeMem.update_struct {mem0 mem : ℕ → ℕ} {nb cap hp0 x off val : ℕ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap) (hval : val ≤ cap)
    (hoff : off = OFF_LEFT ∨ off = OFF_RIGHT ∨ off = OFF_PARENT ∨ off = OFF_PPAR)
    (hs : SafeMem mem0 nb cap hp0 mem) :
    SafeMem mem0 nb cap hp0 (Function.update mem (nb + NODE_STRIDE * x + off) val) := by
  have hoff_lt : off < NODE_STRIDE := by
    rcases hoff with rfl | rfl | rfl | rfl <;> decide
  have ha_lo : nb + NODE_STRIDE ≤ nb + NODE_STRIDE * x + off := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * x := Nat.le_mul_of_pos_right NODE_STRIDE hx1
    omega
  have ha_hi : nb + NODE_STRIDE * x + off < nb + NODE_STRIDE * (cap + 1) := by
    have hmul : NODE_STRIDE * x + NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left NODE_STRIDE (Nat.succ_le_succ hx2)
    omega
  have ha_ne : nb + NODE_STRIDE * x + off ≠ nb - 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Function.update_of_ne ha_ne.symm] using hs.1
  · intro a ha
    have hne : a ≠ nb + NODE_STRIDE * x + off := by
      rcases ha with h | ⟨_, h⟩ | ⟨h, _⟩ <;> omega
    rw [Function.update_of_ne hne]
    exact hs.2.1 a ha
  · intro y hy1 hy2
    by_cases hyx : y = x
    · subst hyx
      rcases hoff with rfl | rfl | rfl | rfl
      · exact ⟨by simpa [nodeField_update_self] using hval,
          by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).2.1,
          by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).2.2⟩
      · exact ⟨by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).1,
          by simpa [nodeField_update_self] using hval,
          by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).2.2⟩
      · exact ⟨by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).1,
          by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).2.1,
          by simpa [nodeField_update_self] using hval⟩
      · exact ⟨by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).1,
          by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).2.1,
          by rw [nodeField_update_ne_off (by decide)]; exact (hs.2.2.1 y hy1 hy2).2.2⟩
    · have hne1 : nodeField (Function.update mem (nb + NODE_STRIDE * x + off) val) nb y OFF_LEFT =
          nodeField mem nb y OFF_LEFT := nodeField_update_ne_node (Ne.symm hyx) hoff_lt (by decide)
      have hne2 : nodeField (Function.update mem (nb + NODE_STRIDE * x + off) val) nb y OFF_RIGHT =
          nodeField mem nb y OFF_RIGHT := nodeField_update_ne_node (Ne.symm hyx) hoff_lt (by decide)
      have hne3 : nodeField (Function.update mem (nb + NODE_STRIDE * x + off) val) nb y OFF_PARENT =
          nodeField mem nb y OFF_PARENT := nodeField_update_ne_node (Ne.symm hyx) hoff_lt (by decide)
      rw [hne1, hne2, hne3]
      exact hs.2.2.1 y hy1 hy2
  · intro y off' hy1 hy2 hoff'
    have hns := ptrOffs_ne_struct hoff'
    have hne_off : off ≠ off' := by
      rcases hoff with rfl | rfl | rfl | rfl
      · exact hns.1.symm
      · exact hns.2.1.symm
      · exact hns.2.2.1.symm
      · exact hns.2.2.2.symm
    by_cases hyx : y = x
    · subst hyx
      rw [nodeField_update_ne_off hne_off]
      exact hs.2.2.2 y off' hy1 hy2 hoff'
    · rw [nodeField_update_ne_node (Ne.symm hyx) hoff_lt (ptrOffs_lt_stride hoff')]
      exact hs.2.2.2 y off' hy1 hy2 hoff'

theorem lctFrame_hdr_eq {b cap : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hfr : LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (cap + 1))
      (lctNodesBase b - 1) m₁ m₂) :
    m₂ (b + LCT_HDR_N) = m₁ (b + LCT_HDR_N) ∧
    m₂ (b + LCT_HDR_CAP) = m₁ (b + LCT_HDR_CAP) ∧
    m₂ (b + LCT_HDR_FREE) = m₁ (b + LCT_HDR_FREE) ∧
    m₂ (b + LCT_HDR_L) = m₁ (b + LCT_HDR_L) ∧
    m₂ (b + LCT_HDR_P) = m₁ (b + LCT_HDR_P) := by
  have hf := hfr.2.2.2.2.2
  unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_N LCT_HDR_CAP LCT_HDR_FREE LCT_HDR_L LCT_HDR_P at *
  refine ⟨hf _ (Or.inl ⟨by omega, by omega⟩),
    hf _ (Or.inl ⟨by omega, by omega⟩),
    hf _ (Or.inl ⟨by omega, by omega⟩),
    hf _ (Or.inl ⟨by omega, by omega⟩),
    hf _ (Or.inl ⟨by omega, by omega⟩)⟩

theorem nodeOwnRawStep_agree_of_nonAgg {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nb cap x p pp : ℕ}
    {l r : AuxTree}
    (ht : TreeMemMatch w h L mem₁ nb cap (.node x l r) p pp)
    (hf_x : ∀ off < NODE_STRIDE,
      off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
      off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
      off ≠ OFF_RIGHT → off ≠ OFF_PARENT → off ≠ OFF_PPAR →
      nodeField mem₂ nb x off = nodeField mem₁ nb x off)
    (hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₁ (nb - 1) → mem₂ a = mem₁ a) :
    nodeOwnRawStep mem₂ nb h L x = nodeOwnRawStep mem₁ nb h L x := by
  have hf_h := hf_x OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  rcases ht with ⟨_, _, _, _, _, _, _, _, hhe_le, _, _, _, _, _, _, _, he1, _⟩
  simp only [nodeOwnRawStep, hf_h]
  by_cases hhe : nodeField mem₁ nb x OFF_HASE = 0
  · simp [hhe]
  · have hhe1 : nodeField mem₁ nb x OFF_HASE = 1 := by omega
    rcases he1 hhe1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, _⟩
    have hf_dir := hf_x OFF_DIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have hf_eid := hf_x OFF_EID (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have hf_eu := hf_x OFF_EU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have hf_ev := hf_x OFF_EV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have hptr : ∀ {off}, off ∈ [OFF_FLOW_PTR, OFF_AF_PTR, OFF_AB_PTR, OFF_COST_FWD, OFF_COST_BWD] →
        NumPtrOk mem₁ (nb + NODE_STRIDE * (cap + 1)) (mem₁ (nb - 1)) h L (nodeField mem₁ nb x off) →
        intVal mem₂ (nodeField mem₂ nb x off) h L = intVal mem₁ (nodeField mem₁ nb x off) h L := by
      intro off hoff hn
      have hf_o : nodeField mem₂ nb x off = nodeField mem₁ nb x off := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
          exact hf_x _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)
      rw [hf_o]
      exact intVal_agree_block fun i hi => hheap _ (le_trans hn.2.1 (Nat.le_add_right _ _))
        (lt_of_lt_of_le (Nat.add_lt_add_left hi _) hn.2.2.1)
    simp only [hhe, ↓reduceIte, hf_dir, hf_eid, hf_eu, hf_ev,
      hptr (by simp) hf_ok, hptr (by simp) haf_ok, hptr (by simp) hab_ok,
      hptr (by simp) hcf_ok, hptr (by simp) hcb_ok]

theorem evalMemSteps_agree_of_nonStruct {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nb cap p pp : ℕ}
    {s : AuxTree}
    (hs : TreeMemMatch w h L mem₁ nb cap s p pp)
    (hs_nd : s.toList.Nodup)
    (hf : ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
      (u = s.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem₂ nb u off = nodeField mem₁ nb u off)
    (hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₁ (nb - 1) → mem₂ a = mem₁ a)
    (flipAcc : Bool) (δAcc : ℤ) :
    evalMemSteps mem₂ nb h L s flipAcc δAcc = evalMemSteps mem₁ nb h L s flipAcc δAcc := by
  induction s generalizing p pp flipAcc δAcc with
  | leaf => rfl
  | node x l r ihl ihr =>
      have hx_t : x ∈ (AuxTree.node x l r).toList := by simp [AuxTree.toList]
      have hown : nodeOwnRawStep mem₂ nb h L x = nodeOwnRawStep mem₁ nb h L x :=
        nodeOwnRawStep_agree_of_nonAgg hs (fun off hlt _ _ _ _ _ _ _ _ _ _ _ _ h13 h14 =>
          hf x hx_t off hlt (fun _ => ⟨h13, h14⟩)) hheap
      have hx_nin_l : x ∉ l.toList := auxTree_nodup_id_nin_left hs_nd
      have hx_nin_r : x ∉ r.toList := auxTree_nodup_id_nin_right hs_nd
      have hfl : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          (u = l.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField mem₂ nb u off = nodeField mem₁ nb u off := fun u hu off hoff _ =>
        hf u (by simp [AuxTree.toList, hu]) off hoff
          (fun heq => absurd heq (fun h => hx_nin_l (by change u = x at h; exact h ▸ hu)))
      have hfr : ∀ u ∈ r.toList, ∀ off < NODE_STRIDE,
          (u = r.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField mem₂ nb u off = nodeField mem₁ nb u off := fun u hu off hoff _ =>
        hf u (by simp [AuxTree.toList, hu]) off hoff
          (fun heq => absurd heq (fun h => hx_nin_r (by change u = x at h; exact h ▸ hu)))
      have hl_eq := ihl hs.children_match.1 (auxTree_nodup_left hs_nd) hfl
      have hr_eq := ihr hs.children_match.2 (auxTree_nodup_right hs_nd) hfr
      have hrev : revFlag mem₂ nb x = revFlag mem₁ nb x := by
        simp [revFlag, hf x hx_t OFF_REV (by decide) (fun _ => ⟨by decide, by decide⟩)]
      have htag : nodeTagInt mem₂ nb h L x = nodeTagInt mem₁ nb h L x := by
        have hht := hf x hx_t OFF_HAS_TAG (by decide) (fun _ => ⟨by decide, by decide⟩)
        have htp := hf x hx_t OFF_TAG_PTR (by decide) (fun _ => ⟨by decide, by decide⟩)
        have htn := hf x hx_t OFF_TAG_NEG (by decide) (fun _ => ⟨by decide, by decide⟩)
        simp only [nodeTagInt, hht, htp, htn]
        by_cases hht0 : nodeField mem₁ nb x OFF_HAS_TAG = 0
        · simp [hht0]
        · have hns := hs.nodeNonStructOk hx_t
          have hht1 : nodeField mem₁ nb x OFF_HAS_TAG = 1 := by have := hns.2.1; omega
          have hnp := hns.2.2.2 hht1
          simp only [hht0, ↓reduceIte, optIntVal, hnp.1]
          have hint : intVal mem₂ (nodeField mem₁ nb x OFF_TAG_PTR) h L =
              intVal mem₁ (nodeField mem₁ nb x OFF_TAG_PTR) h L :=
            intVal_agree_block fun i hi => hheap _ (le_trans hnp.2.1 (Nat.le_add_right _ _))
              (lt_of_lt_of_le (Nat.add_lt_add_left hi _) hnp.2.2.1)
          rw [hint]
      cases flipAcc <;> simp only [evalMemSteps, hown, hrev, htag, hl_eq, hr_eq]

theorem evalMemSteps_nodeId_mem_toList {mem : ℕ → ℕ} {nb h L : ℕ} {t : AuxTree}
    {b : Bool} {δ : ℤ} {s : RawStep} (hs : s ∈ evalMemSteps mem nb h L t b δ) :
    s.nodeId ∈ t.toList := by
  induction t generalizing b δ with
  | leaf => simp [evalMemSteps] at hs
  | node x l r ihl ihr =>
      simp only [evalMemSteps] at hs
      have hown : ∀ b' (u : RawStep),
          u ∈ ((nodeOwnRawStep mem nb h L x).map
            (fun r => (if b' = true then r.flip else r).addDeltaMod h L δ)).toList →
          u.nodeId = x := by
        intro b' u hu
        simp only [Option.mem_toList] at hu
        rcases Option.mem_map.1 hu with ⟨r₀, hr₀, rfl⟩
        rw [RawStep.nodeId_addDeltaMod]
        have hfl : ∀ r : RawStep, (if b' = true then r.flip else r).nodeId = r.nodeId := by
          intro r; cases b' <;> simp [RawStep.nodeId_flip]
        rw [hfl]
        simp only [nodeOwnRawStep, Option.mem_def] at hr₀
        split_ifs at hr₀ <;> cases hr₀ <;> rfl
      rw [AuxTree.toList]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append] at hs ⊢
        rcases hs with (hsl | hso) | hsr
        · exact Or.inl (Or.inl (ihl hsl))
        · exact Or.inl (Or.inr (List.mem_singleton.2 (hown false s hso)))
        · exact Or.inr (ihr hsr)
      · simp only [↓reduceIte, List.mem_append] at hs ⊢
        rcases hs with (hsr | hso) | hsl
        · exact Or.inr (ihr hsr)
        · exact Or.inl (Or.inr (List.mem_singleton.2 (hown true s hso)))
        · exact Or.inl (Or.inl (ihl hsl))

theorem evalMemSteps_split_of_root_zero {mem : ℕ → ℕ} {nb h L x : ℕ} {l r : AuxTree}
    (hrev : revFlag mem nb x = false) (htag : nodeField mem nb x OFF_HAS_TAG = 0) :
    evalMemSteps mem nb h L (.node x l r) false 0 =
      evalMemSteps mem nb h L l false 0 ++
        ((nodeOwnRawStep mem nb h L x).map (fun s => s.addDeltaMod h L 0)).toList ++
        evalMemSteps mem nb h L r false 0 := by
  have hnt : nodeTagInt mem nb h L x = 0 := by simp [nodeTagInt, htag]
  simp only [evalMemSteps, hrev, hnt, Bool.false_xor, ↓reduceIte, Bool.false_eq_true, add_zero]

end MemoryAndSafeHelpers

section ReparentAndPullPre

theorem splayForestOk_reparent_detach {w h L : ℕ} {mem₀ mem₁ : ℕ → ℕ} {nb cap x : ℕ}
    {l r : AuxTree} {rest : List AuxTree}
    (hok₀ : SplayForestOk w h L mem₀ nb cap (.node x l r :: rest))
    (hhp₁ : mem₁ (nb - 1) < 2 ^ w)
    (hpp : nodeField mem₁ nb x OFF_PPAR = nodeField mem₀ nb x OFF_PPAR)
    (htree_x : TreeMemMatch w h L mem₁ nb cap (.node x l .leaf) 0 (nodeField mem₁ nb x OFF_PPAR))
    (hl : ∀ u ≤ cap, u ∉ (AuxTree.node x l .leaf).toList → ∀ off < NODE_STRIDE,
      (r ≠ .leaf → u = r.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem₁ nb u off = nodeField mem₀ nb u off)
    (hr_par : r ≠ .leaf → nodeField mem₁ nb r.rootId OFF_PARENT = 0)
    (hr_pp : r ≠ .leaf → nodeField mem₁ nb r.rootId OFF_PPAR = x)
    (hfr : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem₀ mem₁) :
    SplayForestOk w h L mem₁ nb cap
      (match r with | .leaf => .node x l .leaf :: rest | .node _ _ _ => .node x l .leaf :: r :: rest) ∧
    (∀ s ∈ rest,
      nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false) ∧
    (match r with
      | .leaf => True
      | .node rc _ _ =>
          nodeField mem₁ nb rc OFF_PPAR = x ∧
          r.evalInorder (revFlag mem₁ nb) false = r.evalInorder (revFlag mem₀ nb) false) := by
  have hnd_all₀ : ((AuxTree.node x l r :: rest).flatMap AuxTree.toList).Nodup :=
    hok₀.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hx_nd₀ := hnd_all₀.1
  have hx_tok := hok₀.trees_ok (.node x l r) (by simp)
  have hdisj_x_rest : ∀ a ∈ (AuxTree.node x l r).toList, ∀ b ∈ rest.flatMap AuxTree.toList, a ≠ b :=
    hnd_all₀.2.2
  have hdisj_xl_r : ∀ a ∈ (AuxTree.node x l .leaf).toList, ∀ b ∈ r.toList, a ≠ b := by
    intro a ha b hb
    have hx_nd' := hx_nd₀
    rw [AuxTree.toList, List.nodup_append] at hx_nd'
    have ha' : a ∈ l.toList ++ [x] := by simpa [AuxTree.toList] using ha
    exact hx_nd'.2.2 a ha' b hb
  have hrest_match : ∀ s ∈ rest,
      TreeMemMatch w h L mem₁ nb cap s 0 (nodeField mem₁ nb s.rootId OFF_PPAR) ∧
      nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false := by
    intro s hs
    have hs_ok := hok₀.trees_ok s (by simp [hs])
    have hs_nd : s.toList.Nodup := list_nodup_of_flatMap_nodup hnd_all₀.2.1 hs
    have hdisj_s : ∀ u ∈ s.toList, u ≤ cap ∧ u ∉ (AuxTree.node x l r).toList := fun u hu =>
      ⟨(hs_ok.2.2.nodup_perm_mem hu).2,
       fun hm => hdisj_x_rest u hm u (List.mem_flatMap.2 ⟨s, hs, hu⟩) rfl⟩
    have hf_s : ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
        nodeField mem₁ nb u off = nodeField mem₀ nb u off := by
      intro u hu off hoff
      have hd := hdisj_s u hu
      have hnr : r ≠ .leaf → u ≠ r.rootId := fun hr heq => by
        rw [heq] at hd
        exact hd.2 (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
      have hnx : u ∉ (AuxTree.node x l .leaf).toList := fun hm =>
        hd.2 (by
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm ⊢
          rcases hm with (hl' | rfl) | hleaf
          · exact Or.inl (Or.inl hl')
          · exact Or.inl (Or.inr rfl)
          · simp at hleaf)
      exact hl u hd.1 hnx off hoff (fun hr heq => absurd heq (hnr hr))
    have hpar_s : s ≠ .leaf → nodeField mem₁ nb s.rootId OFF_PARENT = 0 := fun hne => by
      have hm := AuxTree.rootId_mem_toList hne
      rw [hf_s s.rootId hm OFF_PARENT (by decide)]
      cases hs_eq : s with
      | leaf => exact absurd hs_eq hne
      | node sid sl sr =>
          have hs_tm := hs_ok.2.2
          rw [hs_eq] at hs_tm
          exact hs_tm.parent_eq
    have hpp_eq : nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR :=
      hf_s s.rootId (AuxTree.rootId_mem_toList hs_ok.1) OFF_PPAR (by decide)
    have htm : TreeMemMatch w h L mem₁ nb cap s 0 (nodeField mem₁ nb s.rootId OFF_PPAR) := by
      rw [hpp_eq]
      exact treeMemMatch_reparent_root hs_ok.2.2 hs_nd hpar_s (fun _ => hpp_eq)
        (fun u hu off hoff _ => hf_s u hu off hoff) hfr.2.2.1
        (fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩))
    have hev : s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false := by
      apply AuxTree.evalInorder_agree
      intro u hu; simp only [revFlag, hf_s u hu OFF_REV (by decide)]
    exact ⟨htm, hpp_eq, hev⟩
  have hok_base := hok₀
  rcases hok_base with ⟨hh_pos, hwh, hnb3, harena, hL_hdr, hhp₀, _, h0, hperm₀, _⟩
  have h0₁ : SlotZeroOk mem₁ nb := memAgree_slotZero_of_lctFrame (by omega) h0 hfr
  have hL₁ : mem₁ (nb - 3) = L := by
    rw [← hL_hdr]
    exact hfr.2.2.2.2.2 (nb - 3) (Or.inl ⟨by omega, by omega⟩)
  have harena₁ : nb + NODE_STRIDE * (cap + 1) ≤ mem₁ (nb - 1) := le_trans hfr.2.1 hfr.2.2.1
  have hz₁ : ZeroFrom mem₁ (mem₁ (nb - 1)) := hfr.2.2.2.2.1
  have hpp_x_lt : nodeField mem₁ nb x OFF_PPAR < 2 ^ w := by rw [hpp]; exact hx_tok.2.1
  have hrest_out : ∀ s ∈ rest, nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false :=
    fun s hs => (hrest_match s hs).2
  cases r with
  | leaf =>
      have hsf : SplayForestOk w h L mem₁ nb cap (.node x l .leaf :: rest) := by
        refine ⟨hh_pos, hwh, hnb3, harena₁, hL₁, hhp₁, hz₁, h0₁, hperm₀, ?_⟩
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs_rest
        · exact ⟨by simp, by simpa [auxTree_rootId_node] using hpp_x_lt, htree_x⟩
        · have hpp_s_lt : nodeField mem₁ nb s.rootId OFF_PPAR < 2 ^ w := by
            rw [(hrest_match s hs_rest).2.1]
            exact (hok₀.trees_ok s (by simp [hs_rest])).2.1
          exact ⟨(hok₀.trees_ok s (by simp [hs_rest])).1, hpp_s_lt, (hrest_match s hs_rest).1⟩
      exact ⟨hsf, hrest_out, trivial⟩
  | node rc rl rr =>
      have hr_ne : AuxTree.node rc rl rr ≠ .leaf := by simp
      have hrx_tok : TreeMemMatch w h L mem₀ nb cap (.node rc rl rr) x 0 :=
        hx_tok.2.2.children_match.2
      have hr_nd : (AuxTree.node rc rl rr).toList.Nodup := auxTree_nodup_right hx_nd₀
      have hf_r : ∀ u ∈ (AuxTree.node rc rl rr).toList, ∀ off < NODE_STRIDE,
          (u = rc → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField mem₁ nb u off = nodeField mem₀ nb u off := by
        intro u hu off hoff hne_pp
        have hb := (hrx_tok.nodup_perm_mem hu).2
        have hnx : u ∉ (AuxTree.node x l .leaf).toList := fun hm =>
          hdisj_xl_r u hm u hu rfl
        exact hl u hb hnx off hoff (fun _ heq => hne_pp heq)
      have htm_r : TreeMemMatch w h L mem₁ nb cap (.node rc rl rr) 0 x :=
        treeMemMatch_reparent_root hrx_tok hr_nd (fun _ => hr_par hr_ne) (fun _ => hr_pp hr_ne)
          hf_r hfr.2.2.1 (fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩))
      have hev_r : (AuxTree.node rc rl rr).evalInorder (revFlag mem₁ nb) false =
          (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false := by
        apply AuxTree.evalInorder_agree
        intro u hu
        simp only [revFlag, hf_r u hu OFF_REV (by decide) (fun _ => ⟨by decide, by decide⟩)]
      have hperm₁ : ((AuxTree.node x l .leaf :: AuxTree.node rc rl rr :: rest).flatMap AuxTree.toList).Perm
          ((List.range cap).map (· + 1)) := by
        simpa [AuxTree.toList, List.flatMap_cons, List.append_assoc] using hperm₀
      have hx_lt_pow : x < 2 ^ w := by
        have hxb := (hx_tok.2.2.nodup_perm_mem (y := x) (by simp [AuxTree.toList])).2
        have hbase_lt : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := lt_of_le_of_lt harena hhp₀
        unfold NODE_STRIDE at hbase_lt; omega
      have hrc_pp_eq : nodeField mem₁ nb rc OFF_PPAR = x := by simpa [auxTree_rootId_node] using hr_pp hr_ne
      have hsf : SplayForestOk w h L mem₁ nb cap (.node x l .leaf :: .node rc rl rr :: rest) := by
        refine ⟨hh_pos, hwh, hnb3, harena₁, hL₁, hhp₁, hz₁, h0₁, hperm₁, ?_⟩
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | rfl | hs_rest
        · exact ⟨by simp, by simpa [auxTree_rootId_node] using hpp_x_lt, htree_x⟩
        · exact ⟨by simp, by simpa [auxTree_rootId_node, hrc_pp_eq] using hx_lt_pow,
            by simpa [auxTree_rootId_node, hrc_pp_eq] using htm_r⟩
        · have hpp_s_lt : nodeField mem₁ nb s.rootId OFF_PPAR < 2 ^ w := by
            rw [(hrest_match s hs_rest).2.1]
            exact (hok₀.trees_ok s (by simp [hs_rest])).2.1
          exact ⟨(hok₀.trees_ok s (by simp [hs_rest])).1, hpp_s_lt, (hrest_match s hs_rest).1⟩
      exact ⟨hsf, hrest_out, hrc_pp_eq, hev_r⟩

theorem splayForestOk_reparent_splice {w h L : ℕ} {mem₀ mem₂ : ℕ → ℕ} {nb cap p : ℕ}
    {l r_old t_y : AuxTree} {rest : List AuxTree}
    (hok₀ : SplayForestOk w h L mem₀ nb cap (.node p l r_old :: t_y :: rest))
    (hhp₂ : mem₂ (nb - 1) < 2 ^ w)
    (hpp : nodeField mem₂ nb p OFF_PPAR = nodeField mem₀ nb p OFF_PPAR)
    (htree_p : TreeMemMatch w h L mem₂ nb cap (.node p l t_y) 0 (nodeField mem₂ nb p OFF_PPAR))
    (hl : ∀ u ≤ cap, u ∉ (AuxTree.node p l t_y).toList → ∀ off < NODE_STRIDE,
      (r_old ≠ .leaf → u = r_old.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem₂ nb u off = nodeField mem₀ nb u off)
    (hr_par : r_old ≠ .leaf → nodeField mem₂ nb r_old.rootId OFF_PARENT = 0)
    (hr_pp : r_old ≠ .leaf → nodeField mem₂ nb r_old.rootId OFF_PPAR = p)
    (hfr : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem₀ mem₂) :
    SplayForestOk w h L mem₂ nb cap
      (match r_old with | .leaf => .node p l t_y :: rest | .node _ _ _ => .node p l t_y :: r_old :: rest) ∧
    (∀ s ∈ rest,
      nodeField mem₂ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ nb) false = s.evalInorder (revFlag mem₀ nb) false) ∧
    (match r_old with
      | .leaf => True
      | .node rc _ _ =>
          nodeField mem₂ nb rc OFF_PPAR = p ∧
          r_old.evalInorder (revFlag mem₂ nb) false = r_old.evalInorder (revFlag mem₀ nb) false) := by
  have hnd_all₀ : ((AuxTree.node p l r_old :: t_y :: rest).flatMap AuxTree.toList).Nodup :=
    hok₀.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hp_nd₀ := hnd_all₀.1
  have hp_tok := hok₀.trees_ok (.node p l r_old) (by simp)
  have hdisj_pt_rest : ∀ a ∈ (AuxTree.node p l r_old).toList,
      ∀ b ∈ t_y.toList ++ rest.flatMap AuxTree.toList, a ≠ b := hnd_all₀.2.2
  have hdisj_y_rest : ∀ a ∈ t_y.toList, ∀ b ∈ rest.flatMap AuxTree.toList, a ≠ b := hnd_all₀.2.1.2.2
  have hdisj_pl_r : ∀ a ∈ (AuxTree.node p l .leaf).toList, ∀ b ∈ r_old.toList, a ≠ b := by
    intro a ha b hb
    have hp_nd' := hp_nd₀
    rw [AuxTree.toList, List.nodup_append] at hp_nd'
    have ha' : a ∈ l.toList ++ [p] := by simpa [AuxTree.toList] using ha
    exact hp_nd'.2.2 a ha' b hb
  have hrest_match : ∀ s ∈ rest,
      TreeMemMatch w h L mem₂ nb cap s 0 (nodeField mem₂ nb s.rootId OFF_PPAR) ∧
      nodeField mem₂ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ nb) false = s.evalInorder (revFlag mem₀ nb) false := by
    intro s hs
    have hs_ok := hok₀.trees_ok s (by simp [hs])
    have hs_nd : s.toList.Nodup := list_nodup_of_flatMap_nodup hnd_all₀.2.1.2.1 hs
    have hdisj_s : ∀ u ∈ s.toList, u ≤ cap ∧ u ∉ (AuxTree.node p l r_old).toList ∧ u ∉ t_y.toList :=
      fun u hu =>
      ⟨(hs_ok.2.2.nodup_perm_mem hu).2,
       fun hm => hdisj_pt_rest u hm u (List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨s, hs, hu⟩))) rfl,
       fun hm => hdisj_y_rest u hm u (List.mem_flatMap.2 ⟨s, hs, hu⟩) rfl⟩
    have hf_s : ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
        nodeField mem₂ nb u off = nodeField mem₀ nb u off := fun u hu off hoff => by
      rcases hdisj_s u hu with ⟨hb, hnp, hny⟩
      have hnr : r_old ≠ .leaf → u ≠ r_old.rootId := fun hr heq => by
        rw [heq] at hnp
        exact hnp (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
      have hnx : u ∉ (AuxTree.node p l t_y).toList := fun hm => by
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm
        rcases hm with (hl' | rfl) | hy'
        · exact hnp (by simp [AuxTree.toList, hl'])
        · exact hnp (by simp [AuxTree.toList])
        · exact hny hy'
      exact hl u hb hnx off hoff (fun hr heq => absurd heq (hnr hr))
    have hpar_s : s ≠ .leaf → nodeField mem₂ nb s.rootId OFF_PARENT = 0 := fun hne => by
      rw [hf_s s.rootId (AuxTree.rootId_mem_toList hne) OFF_PARENT (by decide)]
      cases hs_eq : s with
      | leaf => exact absurd hs_eq hne
      | node sid sl sr =>
          have hs_tm := hs_ok.2.2
          rw [hs_eq] at hs_tm
          exact hs_tm.parent_eq
    have hpp_eq : nodeField mem₂ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR :=
      hf_s s.rootId (AuxTree.rootId_mem_toList hs_ok.1) OFF_PPAR (by decide)
    have htm : TreeMemMatch w h L mem₂ nb cap s 0 (nodeField mem₂ nb s.rootId OFF_PPAR) := by
      rw [hpp_eq]
      exact treeMemMatch_reparent_root hs_ok.2.2 hs_nd hpar_s (fun _ => hpp_eq)
        (fun u hu off hoff _ => hf_s u hu off hoff) hfr.2.2.1
        (fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩))
    have hev : s.evalInorder (revFlag mem₂ nb) false = s.evalInorder (revFlag mem₀ nb) false := by
      apply AuxTree.evalInorder_agree
      intro u hu; simp only [revFlag, hf_s u hu OFF_REV (by decide)]
    exact ⟨htm, hpp_eq, hev⟩
  have hok_base := hok₀
  rcases hok_base with ⟨hh_pos, hwh, hnb3, harena, hL_hdr, hhp₀, _, h0, hperm₀, _⟩
  have h0₂ : SlotZeroOk mem₂ nb := memAgree_slotZero_of_lctFrame (by omega) h0 hfr
  have hL₂ : mem₂ (nb - 3) = L := by
    rw [← hL_hdr]
    exact hfr.2.2.2.2.2 (nb - 3) (Or.inl ⟨by omega, by omega⟩)
  have harena₂ : nb + NODE_STRIDE * (cap + 1) ≤ mem₂ (nb - 1) := le_trans hfr.2.1 hfr.2.2.1
  have hz₂ : ZeroFrom mem₂ (mem₂ (nb - 1)) := hfr.2.2.2.2.1
  have hpp_p_lt : nodeField mem₂ nb p OFF_PPAR < 2 ^ w := by rw [hpp]; exact hp_tok.2.1
  have hrest_out : ∀ s ∈ rest, nodeField mem₂ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ nb) false = s.evalInorder (revFlag mem₀ nb) false :=
    fun s hs => (hrest_match s hs).2
  cases r_old with
  | leaf =>
      have hperm₂ : ((AuxTree.node p l t_y :: rest).flatMap AuxTree.toList).Perm
          ((List.range cap).map (· + 1)) := by
        simpa [AuxTree.toList, List.flatMap_cons, List.append_assoc] using hperm₀
      have hsf : SplayForestOk w h L mem₂ nb cap (.node p l t_y :: rest) := by
        refine ⟨hh_pos, hwh, hnb3, harena₂, hL₂, hhp₂, hz₂, h0₂, hperm₂, ?_⟩
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs_rest
        · exact ⟨by simp, by simpa [auxTree_rootId_node] using hpp_p_lt, htree_p⟩
        · have hpp_s_lt : nodeField mem₂ nb s.rootId OFF_PPAR < 2 ^ w := by
            rw [(hrest_match s hs_rest).2.1]
            exact (hok₀.trees_ok s (by simp [hs_rest])).2.1
          exact ⟨(hok₀.trees_ok s (by simp [hs_rest])).1, hpp_s_lt, (hrest_match s hs_rest).1⟩
      exact ⟨hsf, hrest_out, trivial⟩
  | node rc rl rr =>
      have hr_ne : AuxTree.node rc rl rr ≠ .leaf := by simp
      have hr_tok : TreeMemMatch w h L mem₀ nb cap (.node rc rl rr) p 0 :=
        hp_tok.2.2.children_match.2
      have hr_nd : (AuxTree.node rc rl rr).toList.Nodup := auxTree_nodup_right hp_nd₀
      have hf_r : ∀ u ∈ (AuxTree.node rc rl rr).toList, ∀ off < NODE_STRIDE,
          (u = rc → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField mem₂ nb u off = nodeField mem₀ nb u off := by
        intro u hu off hoff hne_pp
        have hb := (hr_tok.nodup_perm_mem hu).2
        have hnx : u ∉ (AuxTree.node p l t_y).toList := fun hm => by
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm
          rcases hm with (hl' | rfl) | hy'
          · exact hdisj_pl_r u (by simp [AuxTree.toList, hl']) u hu rfl
          · exact hdisj_pl_r u (by simp [AuxTree.toList]) u hu rfl
          · have hu_t : u ∈ (AuxTree.node p l (.node rc rl rr)).toList := by
              rw [AuxTree.toList, List.mem_append]; exact Or.inr hu
            exact hdisj_pt_rest u hu_t u (List.mem_append.2 (Or.inl hy')) rfl
        exact hl u hb hnx off hoff (fun _ heq => hne_pp heq)
      have htm_r : TreeMemMatch w h L mem₂ nb cap (.node rc rl rr) 0 p :=
        treeMemMatch_reparent_root hr_tok hr_nd (fun _ => hr_par hr_ne) (fun _ => hr_pp hr_ne)
          hf_r hfr.2.2.1 (fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩))
      have hev_r : (AuxTree.node rc rl rr).evalInorder (revFlag mem₂ nb) false =
          (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false := by
        apply AuxTree.evalInorder_agree
        intro u hu
        simp only [revFlag, hf_r u hu OFF_REV (by decide) (fun _ => ⟨by decide, by decide⟩)]
      have hperm₂ : ((AuxTree.node p l t_y :: AuxTree.node rc rl rr :: rest).flatMap AuxTree.toList).Perm
          ((List.range cap).map (· + 1)) := by
        have h1 : (AuxTree.node p l t_y).toList ++ (AuxTree.node rc rl rr).toList =
            l.toList ++ [p] ++ t_y.toList ++ (AuxTree.node rc rl rr).toList := by
          simp [AuxTree.toList, List.append_assoc]
        have h2 : (AuxTree.node p l (AuxTree.node rc rl rr)).toList ++ t_y.toList =
            l.toList ++ [p] ++ (AuxTree.node rc rl rr).toList ++ t_y.toList := by
          simp [AuxTree.toList, List.append_assoc]
        have hswap : (t_y.toList ++ (AuxTree.node rc rl rr).toList).Perm
            ((AuxTree.node rc rl rr).toList ++ t_y.toList) := List.perm_append_comm
        have hhead : ((AuxTree.node p l t_y).toList ++ (AuxTree.node rc rl rr).toList).Perm
            ((AuxTree.node p l (AuxTree.node rc rl rr)).toList ++ t_y.toList) := by
          rw [h1, h2]
          simpa only [List.append_assoc] using List.Perm.append_left (l.toList ++ [p]) hswap
        simp only [List.flatMap_cons] at hperm₀ ⊢
        rw [← List.append_assoc] at hperm₀ ⊢
        exact (hhead.append_right _).trans hperm₀
      have hp_lt_pow : p < 2 ^ w := by
        have hpb := (hp_tok.2.2.nodup_perm_mem (y := p) (by simp [AuxTree.toList])).2
        have hbase_lt : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := lt_of_le_of_lt harena hhp₀
        unfold NODE_STRIDE at hbase_lt; omega
      have hrc_pp_eq : nodeField mem₂ nb rc OFF_PPAR = p := by simpa [auxTree_rootId_node] using hr_pp hr_ne
      have hsf : SplayForestOk w h L mem₂ nb cap (.node p l t_y :: .node rc rl rr :: rest) := by
        refine ⟨hh_pos, hwh, hnb3, harena₂, hL₂, hhp₂, hz₂, h0₂, hperm₂, ?_⟩
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | rfl | hs_rest
        · exact ⟨by simp, by simpa [auxTree_rootId_node] using hpp_p_lt, htree_p⟩
        · exact ⟨by simp, by simpa [auxTree_rootId_node, hrc_pp_eq] using hp_lt_pow,
            by simpa [auxTree_rootId_node, hrc_pp_eq] using htm_r⟩
        · have hpp_s_lt : nodeField mem₂ nb s.rootId OFF_PPAR < 2 ^ w := by
            rw [(hrest_match s hs_rest).2.1]
            exact (hok₀.trees_ok s (by simp [hs_rest])).2.1
          exact ⟨(hok₀.trees_ok s (by simp [hs_rest])).1, hpp_s_lt, (hrest_match s hs_rest).1⟩
      exact ⟨hsf, hrest_out, hrc_pp_eq, hev_r⟩

theorem pullPre_detach {w h L : ℕ} {mem₀ mem_ptr : ℕ → ℕ} {nb cap x pp : ℕ}
    {l r : AuxTree}
    (hbase : nb + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hsrc : TreeMemMatch w h L mem₀ nb cap (.node x l r) 0 pp)
    (hx_nd : (AuxTree.node x l r).toList.Nodup)
    (hrev0 : nodeField mem₀ nb x OFF_REV = 0)
    (hht0 : nodeField mem₀ nb x OFF_HAS_TAG = 0)
    (hhp_eq : mem_ptr (nb - 1) = mem₀ (nb - 1))
    (hL : nodeField mem_ptr nb x OFF_LEFT = l.rootId)
    (hR : nodeField mem_ptr nb x OFF_RIGHT = 0)
    (hP : nodeField mem_ptr nb x OFF_PARENT = 0)
    (hPP : nodeField mem_ptr nb x OFF_PPAR = pp)
    (hx_other : ∀ off < NODE_STRIDE, off ≠ OFF_RIGHT →
      nodeField mem_ptr nb x off = nodeField mem₀ nb x off)
    (hl_fields : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
      nodeField mem_ptr nb u off = nodeField mem₀ nb u off)
    (hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nb - 1) → mem_ptr a = mem₀ a) :
    PullPre w h L mem_ptr nb cap x l .leaf 0 pp := by
  have hx_nin_l : x ∉ l.toList := auxTree_nodup_id_nin_left hx_nd
  have hl_nd : l.toList.Nodup := auxTree_nodup_left hx_nd
  have hl_m : TreeMemMatch w h L mem_ptr nb cap l x 0 :=
    treeMemMatch_reparent_root hsrc.children_match.1 hl_nd
      (fun hne => by
        rw [hl_fields _ (AuxTree.rootId_mem_toList hne) OFF_PARENT (by decide)]
        cases hl_eq : l with
        | leaf => exact absurd hl_eq hne
        | node lid ll lr =>
            have htm := hsrc.children_match.1; rw [hl_eq] at htm; exact htm.parent_eq)
      (fun hne => by
        rw [hl_fields _ (AuxTree.rootId_mem_toList hne) OFF_PPAR (by decide)]
        cases hl_eq : l with
        | leaf => exact absurd hl_eq hne
        | node lid ll lr =>
            have htm := hsrc.children_match.1; rw [hl_eq] at htm; exact htm.2.2.2.2.2.1)
      (fun u hu off hoff _ => hl_fields u hu off hoff)
      (by omega) hheap
  have hvc : listVcnt mem_ptr nb
      (l.evalInorder (revFlag mem_ptr nb) false ++ [x] ++
        AuxTree.leaf.evalInorder (revFlag mem_ptr nb) false) < 2 ^ w := by
    simp only [AuxTree.evalInorder, List.append_nil]
    have hnd_seq : (l.evalInorder (revFlag mem_ptr nb) false ++ [x]).Nodup := by
      have hp : (l.evalInorder (revFlag mem_ptr nb) false ++ [x]).Perm (l.toList ++ [x]) :=
        (l.evalInorder_perm _ _).append_right [x]
      exact hp.nodup_iff.2 (List.nodup_append.2 ⟨hl_nd, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.1 hb]; intro heq; subst heq; exact hx_nin_l ha⟩)
    apply listVcnt_lt_pow_of_le hbase hnd_seq
    · intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hul | rfl
      · exact hsrc.nodup_perm_mem (by simp [AuxTree.toList, (l.evalInorder_perm _ _).mem_iff.1 hul])
      · exact hsrc.nodup_perm_mem (by simp [AuxTree.toList])
    · intro u hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hul | rfl
      · have hm := (l.evalInorder_perm _ _).mem_iff.1 hul
        rw [hl_fields u hm OFF_ISV (by decide)]
        exact listIsv_bound_of_tree hsrc (by simp [AuxTree.toList, hm])
      · rw [hx_other OFF_ISV (by decide) (by decide)]
        exact listIsv_bound_of_tree hsrc (by simp [AuxTree.toList])
  exact pullPre_of_nonStruct_agree hsrc (by simp [AuxTree.toList]) (by omega) hheap
    (fun off hns => hx_other off hns.1 (fun h => by subst h; simp [IsNonStructNonAggOff] at hns))
    hL (by simpa [AuxTree.rootId] using hR) hP hPP hrev0 hht0 hl_m trivial hvc

theorem pullPre_splice {w h L : ℕ} {mem₀ mem_ptr : ℕ → ℕ} {nb cap p : ℕ}
    {l r_old t_y : AuxTree}
    (hbase : nb + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hsrc : TreeMemMatch w h L mem₀ nb cap (.node p l r_old) 0 (nodeField mem₀ nb p OFF_PPAR))
    (hp_nd : (AuxTree.node p l r_old).toList.Nodup)
    (hy_src : TreeMemMatch w h L mem₀ nb cap t_y 0 p)
    (hy_nd : t_y.toList.Nodup)
    (hdisj_pt : ∀ a ∈ (AuxTree.node p l r_old).toList, ∀ b ∈ t_y.toList, a ≠ b)
    (hrev0 : nodeField mem₀ nb p OFF_REV = 0)
    (hht0 : nodeField mem₀ nb p OFF_HAS_TAG = 0)
    (hhp_eq : mem_ptr (nb - 1) = mem₀ (nb - 1))
    (hL : nodeField mem_ptr nb p OFF_LEFT = l.rootId)
    (hR : nodeField mem_ptr nb p OFF_RIGHT = t_y.rootId)
    (hP : nodeField mem_ptr nb p OFF_PARENT = 0)
    (hPP : nodeField mem_ptr nb p OFF_PPAR = nodeField mem₀ nb p OFF_PPAR)
    (hy_par : nodeField mem_ptr nb t_y.rootId OFF_PARENT = p)
    (hy_pp : nodeField mem_ptr nb t_y.rootId OFF_PPAR = 0)
    (hp_other : ∀ off < NODE_STRIDE, off ≠ OFF_RIGHT →
      nodeField mem_ptr nb p off = nodeField mem₀ nb p off)
    (hl_fields : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
      nodeField mem_ptr nb u off = nodeField mem₀ nb u off)
    (hy_fields : ∀ u ∈ t_y.toList, ∀ off < NODE_STRIDE,
      (u = t_y.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem_ptr nb u off = nodeField mem₀ nb u off)
    (hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nb - 1) → mem_ptr a = mem₀ a) :
    PullPre w h L mem_ptr nb cap p l t_y 0 (nodeField mem₀ nb p OFF_PPAR) := by
  have hp_nin_l : p ∉ l.toList := auxTree_nodup_id_nin_left hp_nd
  have hl_nd : l.toList.Nodup := auxTree_nodup_left hp_nd
  have hl_m : TreeMemMatch w h L mem_ptr nb cap l p 0 :=
    treeMemMatch_reparent_root hsrc.children_match.1 hl_nd
      (fun hne => by
        rw [hl_fields _ (AuxTree.rootId_mem_toList hne) OFF_PARENT (by decide)]
        cases hl_eq : l with
        | leaf => exact absurd hl_eq hne
        | node lid ll lr =>
            have htm := hsrc.children_match.1; rw [hl_eq] at htm; exact htm.parent_eq)
      (fun hne => by
        rw [hl_fields _ (AuxTree.rootId_mem_toList hne) OFF_PPAR (by decide)]
        cases hl_eq : l with
        | leaf => exact absurd hl_eq hne
        | node lid ll lr =>
            have htm := hsrc.children_match.1; rw [hl_eq] at htm; exact htm.2.2.2.2.2.1)
      (fun u hu off hoff _ => hl_fields u hu off hoff)
      (by omega) hheap
  have hy_m : TreeMemMatch w h L mem_ptr nb cap t_y p 0 :=
    treeMemMatch_reparent_root hy_src hy_nd (fun _ => hy_par) (fun _ => hy_pp) hy_fields
      (by omega) hheap
  have hvc : listVcnt mem_ptr nb
      (l.evalInorder (revFlag mem_ptr nb) false ++ [p] ++
        t_y.evalInorder (revFlag mem_ptr nb) false) < 2 ^ w := by
    have hperm_seq : (l.evalInorder (revFlag mem_ptr nb) false ++ [p] ++
        t_y.evalInorder (revFlag mem_ptr nb) false).Perm ((l.toList ++ [p]) ++ t_y.toList) :=
      ((l.evalInorder_perm _ _).append_right [p]).append (t_y.evalInorder_perm _ _)
    have hnd_pt : ((l.toList ++ [p]) ++ t_y.toList).Nodup := by
      rw [List.nodup_append]
      refine ⟨List.nodup_append.2 ⟨hl_nd, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.1 hb]; intro h; subst h; exact hp_nin_l ha⟩, hy_nd, ?_⟩
      intro a ha b hb
      rcases List.mem_append.1 ha with hal | hap
      · exact hdisj_pt a (by simp [AuxTree.toList, hal]) b hb
      · rw [List.mem_singleton.1 hap]; exact hdisj_pt p (by simp [AuxTree.toList]) b hb
    apply listVcnt_lt_pow_of_le hbase (hperm_seq.nodup_iff.2 hnd_pt)
    · intro u hu
      have hum := hperm_seq.mem_iff.1 hu
      simp only [List.mem_append, List.mem_singleton] at hum
      rcases hum with (hul | rfl) | huy
      · exact hsrc.nodup_perm_mem (by simp [AuxTree.toList, hul])
      · exact hsrc.nodup_perm_mem (by simp [AuxTree.toList])
      · exact hy_src.nodup_perm_mem huy
    · intro u hu
      have hum := hperm_seq.mem_iff.1 hu
      simp only [List.mem_append, List.mem_singleton] at hum
      rcases hum with (hul | rfl) | huy
      · rw [hl_fields u hul OFF_ISV (by decide)]
        exact listIsv_bound_of_tree hsrc (by simp [AuxTree.toList, hul])
      · rw [hp_other OFF_ISV (by decide) (by decide)]
        exact listIsv_bound_of_tree hsrc (by simp [AuxTree.toList])
      · rw [hy_fields u huy OFF_ISV (by decide) (fun _ => ⟨by decide, by decide⟩)]
        exact listIsv_bound_of_tree hy_src huy
  exact pullPre_of_nonStruct_agree hsrc (by simp [AuxTree.toList]) (by omega) hheap
    (fun off hns => hp_other off hns.1 (fun h => by subst h; simp [IsNonStructNonAggOff] at hns))
    hL hR hP hPP hrev0 hht0 hl_m hy_m hvc

end ReparentAndPullPre

end MinCostFlow.LinkCut.Prog
