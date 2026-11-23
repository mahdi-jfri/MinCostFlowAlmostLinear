module

public import MinCostFlow.LinkCut.Prog.SplayStepPullExec

namespace MinCostFlow.LinkCut.Prog

/-!
`WordRAM` postcondition proof for `pullBody`:
- `pullBody_runs` upgrading `PullPre` to `TreeMemMatch w h L st'.mem nodesBase cap (.node x l r) parId pp`
  plus `LctFrame` and amortized step+heap bound `K_PULL L`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

/-! ### Main `pullBody` specification -/

private theorem addr_ne_of_outside_slot {addr ptr : ℕ}
    (hout : addr < ptr ∨ ptr + NODE_STRIDE ≤ addr) {off : ℕ} (hoff : off < NODE_STRIDE) :
    addr ≠ ptr + off := by omega

private theorem slot_addr_disj_of_ne {nb x u off : ℕ} (hux : u ≠ x) (hoff : off < NODE_STRIDE) :
    nb + NODE_STRIDE * u + off < nb + NODE_STRIDE * x ∨
      nb + NODE_STRIDE * x + NODE_STRIDE ≤ nb + NODE_STRIDE * u + off := by
  unfold NODE_STRIDE at hoff ⊢
  rcases lt_or_gt_of_ne hux with h | h <;> omega

private theorem slot_addr_lt_arenaHi {nb cap u off : ℕ}
    (hu : u ≤ cap) (hoff : off < NODE_STRIDE) :
    nb + NODE_STRIDE * u + off < nb + NODE_STRIDE * (cap + 1) := by
  unfold NODE_STRIDE at hoff ⊢
  omega

private theorem slot_addr_ne_nb1 {nb u off : ℕ} (hnb : 3 ≤ nb) (hu : 1 ≤ u) :
    nb + NODE_STRIDE * u + off ≠ nb - 1 := by
  unfold NODE_STRIDE
  omega

private theorem node_lt_arenaHi {nb cap u : ℕ} (hu : u ≤ cap) :
    nb + NODE_STRIDE * u + NODE_STRIDE ≤ nb + NODE_STRIDE * (cap + 1) := by
  unfold NODE_STRIDE
  omega

private theorem sub_split_le {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    c - a = (b - a) + (c - b) := by omega

theorem pullBody_runs {w h L nodesBase cap x parId pp : ℕ}
    (p : Program) (sp : SplayProcs) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + 4 * L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {l r : AuxTree} (hx_nin_l : x ∉ l.toList) (hx_nin_r : x ∉ r.toList)
    (hpre : PullPre w h L mem₀ nodesBase cap x l r parId pp) :
    ∀ ω, ∃ st' c,
      Runs w p ω (pullBody sp) (startState [nodesBase, x] mem₀ pos) (.returned 0) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_PULL L ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 4 * L ∧
      TreeMemMatch w h L st'.mem nodesBase cap (.node x l r) parId pp ∧
      (∀ addr, addr ≠ nodesBase - 1 →
        (addr < nodesBase + NODE_STRIDE * x ∨
          nodesBase + NODE_STRIDE * x + NODE_STRIDE ≤ addr) →
        addr < mem₀ (nodesBase - 1) →
        st'.mem addr = mem₀ addr) ∧
      (∀ off < NODE_STRIDE, off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
        off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
        off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
        nodeField st'.mem nodesBase x off = nodeField mem₀ nodesBase x off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  intro ω
  let st0 := startState [nodesBase, x] mem₀ pos
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let hp₀ := mem₀ (nodesBase - 1)
  let ptr := nodesBase + NODE_STRIDE * x
  let lPtr := nodesBase + NODE_STRIDE * l.rootId
  let rPtr := nodesBase + NODE_STRIDE * r.rootId
  have hx1 := hpre.hx1
  have hx2 := hpre.hx2
  have hl_le : l.rootId ≤ cap := by
    cases l with
    | leaf => simp [AuxTree.rootId]
    | node lid _ _ => exact (hpre.hl.nodup_perm_mem (by simp [AuxTree.rootId, AuxTree.toList])).2
  have hr_le : r.rootId ≤ cap := by
    cases r with
    | leaf => simp [AuxTree.rootId]
    | node rid _ _ => exact (hpre.hr.nodup_perm_mem (by simp [AuxTree.rootId, AuxTree.toList])).2
  have hx_ne_l : x ≠ l.rootId := by
    cases l with
    | leaf => simp [AuxTree.rootId]; omega
    | node lid _ _ => intro h; subst h; exact hx_nin_l (by simp [AuxTree.toList])
  have hx_ne_r : x ≠ r.rootId := by
    cases r with
    | leaf => simp [AuxTree.rootId]; omega
    | node rid _ _ => intro h; subst h; exact hx_nin_r (by simp [AuxTree.toList])
  have hx_arena : ptr + NODE_STRIDE ≤ arenaHi := node_lt_arenaHi hx2
  have hl_arena : lPtr + NODE_STRIDE ≤ arenaHi := node_lt_arenaHi hl_le
  have hr_arena : rPtr + NODE_STRIDE ≤ arenaHi := node_lt_arenaHi hr_le
  have harena_pos : 1 ≤ arenaHi := by
    have : 1 ≤ nodesBase := le_trans (by decide) hnb
    exact le_trans this (Nat.le_add_right _ _)
  have hptr_off_lt_ar : ∀ off < NODE_STRIDE, ptr + off < arenaHi := fun off hoff =>
    lt_of_lt_of_le (Nat.add_lt_add_left hoff ptr) hx_arena
  have hptr_off_lt_hp : ∀ off < NODE_STRIDE, ptr + off < hp₀ := fun off hoff =>
    lt_of_lt_of_le (hptr_off_lt_ar off hoff) harena
  have hl_off_lt_hp : ∀ off < NODE_STRIDE, lPtr + off < hp₀ := fun off hoff =>
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hoff lPtr) hl_arena) harena
  have hr_off_lt_hp : ∀ off < NODE_STRIDE, rPtr + off < hp₀ := fun off hoff =>
    lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hoff rPtr) hr_arena) harena
  have h_ge_hp_ne : ∀ a off, hp₀ ≤ a → off < NODE_STRIDE → a ≠ ptr + off := fun a off ha hoff =>
    Nat.ne_of_gt (lt_of_lt_of_le (hptr_off_lt_hp off hoff) ha)
  have h_ar_ne : ∀ a off, arenaHi ≤ a → off < NODE_STRIDE → a ≠ ptr + off := fun a off ha hoff =>
    Nat.ne_of_gt (lt_of_lt_of_le (hptr_off_lt_ar off hoff) ha)
  have h_slot_ne : ∀ {o1 o2 : ℕ}, o1 ≠ o2 → ptr + o1 ≠ ptr + o2 := fun h heq =>
    h (Nat.add_left_cancel heq)
  have hnb1_lt_ptr : nodesBase - 1 < ptr := by
    have : nodesBase - 1 < nodesBase := Nat.sub_lt (le_trans (by decide) hnb) (by decide)
    exact lt_of_lt_of_le this (Nat.le_add_right _ _)
  have hnb1_ne_slot : ∀ off, nodesBase - 1 ≠ ptr + off := fun off =>
    Nat.ne_of_lt (lt_of_lt_of_le hnb1_lt_ptr (Nat.le_add_right _ _))
  have hnb1_ne_ar : ∀ a, arenaHi ≤ a → a ≠ nodesBase - 1 := fun a ha => by
    have : nodesBase - 1 < nodesBase := Nat.sub_lt (le_trans (by decide) hnb) (by decide)
    exact Nat.ne_of_gt (lt_of_lt_of_le this (le_trans (Nat.le_add_right _ _) ha))
  have h4L2 : 2 * L + 2 * L = 4 * L := by ring
  have h2L4L : 2 * L ≤ 4 * L := by omega
  have hal_x : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w := fun off hoff => nodeAddr_lt_pow hbase hx2 hoff
  have hal_l : ∀ off < NODE_STRIDE, lPtr + off < 2 ^ w := fun off hoff => nodeAddr_lt_pow hbase hl_le hoff
  have hal_r : ∀ off < NODE_STRIDE, rPtr + off < 2 ^ w := fun off hoff => nodeAddr_lt_pow hbase hr_le hoff
  have hdisj_l : ∀ o1 < NODE_STRIDE, ∀ o2 < NODE_STRIDE, ptr + o1 ≠ lPtr + o2 := fun o1 ho1 o2 ho2 =>
    addr_ne_of_outside_slot (slot_addr_disj_of_ne hx_ne_l ho1) ho2
  have hdisj_r : ∀ o1 < NODE_STRIDE, ∀ o2 < NODE_STRIDE, ptr + o1 ≠ rPtr + o2 := fun o1 ho1 o2 ho2 =>
    addr_ne_of_outside_slot (slot_addr_disj_of_ne hx_ne_r ho1) ho2
  have hL_lt : L < 2 ^ w := by
    by_cases hLz : L = 0
    · rw [hLz]; exact Nat.pow_pos (by decide)
    · have h4L : L ≤ 4 * L := Nat.le_mul_of_pos_left L (by decide)
      have : hp₀ + L ≤ hp₀ + 4 * L := Nat.add_le_add_left h4L hp₀
      have h1 : L ≤ hp₀ + L := Nat.le_add_left L hp₀
      exact lt_of_le_of_lt (Nat.le_trans h1 this) hhp_lt
  have hhp₀_lt : hp₀ < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right hp₀ (4 * L)) hhp_lt
  let seq_l := l.evalInorder (revFlag mem₀ nodesBase) false
  let seq_r := r.evalInorder (revFlag mem₀ nodesBase) false
  let seq := seq_l ++ [x] ++ seq_r
  have hvc_l : nodeField mem₀ nodesBase l.rootId OFF_VCNT = listVcnt mem₀ nodesBase seq_l :=
    (hpre.hl.rootAggs h0).1
  have hvc_r : nodeField mem₀ nodesBase r.rootId OFF_VCNT = listVcnt mem₀ nodesBase seq_r :=
    (hpre.hr.rootAggs h0).1
  have hvc_sum : (listVcnt mem₀ nodesBase seq_l + nodeField mem₀ nodesBase x OFF_ISV) +
      listVcnt mem₀ nodesBase seq_r = listVcnt mem₀ nodesBase seq := by
    simp only [seq, listVcnt_append, listVcnt]; omega
  have hvc1_lt : mem₀ (lPtr + OFF_VCNT) + mem₀ (ptr + OFF_ISV) < 2 ^ w := by
    change nodeField mem₀ nodesBase l.rootId OFF_VCNT + nodeField mem₀ nodesBase x OFF_ISV < 2 ^ w
    rw [hvc_l]; have := hpre.hvcnt_lt; dsimp only [seq, seq_l, seq_r] at hvc_sum ⊢; omega
  have hvc_eq : mem₀ (lPtr + OFF_VCNT) + mem₀ (ptr + OFF_ISV) + mem₀ (rPtr + OFF_VCNT) =
      listVcnt mem₀ nodesBase seq := by
    change nodeField mem₀ nodesBase l.rootId OFF_VCNT + nodeField mem₀ nodesBase x OFF_ISV +
      nodeField mem₀ nodesBase r.rootId OFF_VCNT = _
    rw [hvc_l, hvc_r, hvc_sum]
  have hvc2_lt : listVcnt mem₀ nodesBase seq < 2 ^ w := hpre.hvcnt_lt
  rcases pullPtrs_exec hbase hx2 hl_le hr_le hpre.hL hpre.hR st0 rfl rfl rfl with
    ⟨st1, hr_ptrs, hm1, h1_0, h1_1, h1_2, h1_4, h1_6⟩
  rcases pullVcntHdr_exec hnb (by simp [ptr]) hL_hdr rfl hL_lt hhp₀_lt
      (hal_l OFF_VCNT (by decide)) (hal_x OFF_ISV (by decide))
      (hal_r OFF_VCNT (by decide)) (hal_x OFF_VCNT (by decide))
      hvc1_lt hvc_eq hvc2_lt st1 hm1 h1_0 h1_1 h1_2 h1_4 h1_6 with
    ⟨st2, hr_vcnt, hm2, h2_0, h2_1, h2_2, h2_4, h2_6, h2_15, h2_16⟩
  have h2_other : ∀ a, a ≠ ptr + OFF_VCNT → st2.mem a = mem₀ a := fun a ha => by
    rw [hm2]; exact Function.update_of_ne ha _ _
  have h2_hz : ZeroFrom st2.mem hp₀ := fun a ha => by
    rw [h2_other a (h_ge_hp_ne a OFF_VCNT ha (by decide))]; exact hz a ha
  rcases treeMemMatch_rootOptCsumOk h0 hpre.hl with ⟨hl_cf_ok, hl_cb_ok⟩
  rcases treeMemMatch_rootOptCsumOk h0 hpre.hr with ⟨hr_cf_ok, hr_cb_ok⟩
  have hx_cf_ok : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase x OFF_COST_FWD) := by
    by_cases he : nodeField mem₀ nodesBase x OFF_HASE = 0
    · exact Or.inl (hpre.he0 he).2.2.2.2.1
    · have h1 := eq_one_of_le_one_ne_zero hpre.hhe he
      have hk := (hpre.he1 h1).2.2.2.1
      exact Or.inr ⟨hk.2.1, hk.2.2.1, hk.2.2.2⟩
  have hx_cb_ok : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase x OFF_COST_BWD) := by
    by_cases he : nodeField mem₀ nodesBase x OFF_HASE = 0
    · exact Or.inl (hpre.he0 he).2.2.2.2.2
    · have h1 := eq_one_of_le_one_ne_zero hpre.hhe he
      have hk := (hpre.he1 h1).2.2.2.2.1
      exact Or.inr ⟨hk.2.1, hk.2.2.1, hk.2.2.2⟩
  have hag20 : ∀ a, arenaHi ≤ a → a < hp₀ → st2.mem a = mem₀ a := fun a ha _ =>
    h2_other a (h_ar_ne a OFF_VCNT ha (by decide))
  have h2_l_cf : OptNumPtrOk st2.mem arenaHi hp₀ h L (st2.mem (lPtr + OFF_CSUM_FWD)) := by
    rw [h2_other _ (hdisj_l _ (by decide) _ (by decide)).symm]
    exact optNumPtrOk_congr le_rfl hag20 hl_cf_ok
  have h2_x_cf : OptNumPtrOk st2.mem arenaHi hp₀ h L (st2.mem (ptr + OFF_COST_FWD)) := by
    rw [h2_other _ (h_slot_ne (by decide))]
    exact optNumPtrOk_congr le_rfl hag20 hx_cf_ok
  have h2_r_cf : OptNumPtrOk st2.mem arenaHi hp₀ h L (st2.mem (rPtr + OFF_CSUM_FWD)) := by
    rw [h2_other _ (hdisj_r _ (by decide) _ (by decide)).symm]
    exact optNumPtrOk_congr le_rfl hag20 hr_cf_ok
  rcases pullCsumPair_exec hp_ok harena_pos harena (by omega) (by decide) (by decide)
      hl_arena hx_arena hr_arena st2 h2_hz h2_0 h2_1 h2_2 h2_4 h2_6 h2_15 h2_16
      h2_l_cf h2_x_cf h2_r_cf with
    ⟨st3, c_fwd, hp1, hr_fwd, h3_0, h3_1, h3_2, h3_4, h3_6, h3_15, h3_16,
      hle1, hhi1, hc_fwd, hpres3, hz3, h3_cf_ok, h3_cf_val⟩
  have h3_lt_hp0 : ∀ a < hp₀, a ≠ ptr + OFF_VCNT → a ≠ ptr + OFF_CSUM_FWD → st3.mem a = mem₀ a :=
    fun a ha h1 h2 => (hpres3 a ha h2).trans (h2_other a h1)
  have hag30 : ∀ a, arenaHi ≤ a → a < hp₀ → st3.mem a = mem₀ a := fun a ha1 ha2 =>
    h3_lt_hp0 a ha2 (h_ar_ne a OFF_VCNT ha1 (by decide)) (h_ar_ne a OFF_CSUM_FWD ha1 (by decide))
  have h3_l_cb : OptNumPtrOk st3.mem arenaHi hp1 h L (st3.mem (lPtr + OFF_CSUM_BWD)) := by
    rw [h3_lt_hp0 _ (hl_off_lt_hp OFF_CSUM_BWD (by decide))
      (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm]
    exact optNumPtrOk_congr hle1 hag30 hl_cb_ok
  have h3_x_cb : OptNumPtrOk st3.mem arenaHi hp1 h L (st3.mem (ptr + OFF_COST_BWD)) := by
    rw [h3_lt_hp0 _ (hptr_off_lt_hp OFF_COST_BWD (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
    exact optNumPtrOk_congr hle1 hag30 hx_cb_ok
  have h3_r_cb : OptNumPtrOk st3.mem arenaHi hp1 h L (st3.mem (rPtr + OFF_CSUM_BWD)) := by
    rw [h3_lt_hp0 _ (hr_off_lt_hp OFF_CSUM_BWD (by decide))
      (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm]
    exact optNumPtrOk_congr hle1 hag30 hr_cb_ok
  rcases pullCsumPair_exec hp_ok harena_pos (le_trans harena hle1) (by omega) (by decide) (by decide)
      hl_arena hx_arena hr_arena st3 hz3 h3_0 h3_1 h3_2 h3_4 h3_6 h3_15 h3_16
      h3_l_cb h3_x_cb h3_r_cb with
    ⟨st4, c_bwd, hp2, hr_bwd, h4_0, h4_1, h4_2, h4_4, h4_6, h4_15, h4_16,
      hle2, hhi2, hc_bwd, hpres4, hz4, h4_cb_ok, h4_cb_val⟩
  have h4_lt_hp0 : ∀ a < hp₀, a ≠ ptr + OFF_VCNT → a ≠ ptr + OFF_CSUM_FWD →
      a ≠ ptr + OFF_CSUM_BWD → st4.mem a = mem₀ a :=
    fun a ha h1 h2 h3 => (hpres4 a (lt_of_lt_of_le ha hle1) h3).trans (h3_lt_hp0 a ha h1 h2)
  have hag40 : ∀ a, arenaHi ≤ a → a < hp₀ → st4.mem a = mem₀ a := fun a ha1 ha2 =>
    h4_lt_hp0 a ha2 (h_ar_ne a OFF_VCNT ha1 (by decide))
      (h_ar_ne a OFF_CSUM_FWD ha1 (by decide)) (h_ar_ne a OFF_CSUM_BWD ha1 (by decide))
  have hl_ca1 : CanonicalNumAgg st4.mem arenaHi hp2 h L
      (st4.mem (lPtr + OFF_MIN1_HAS)) (st4.mem (lPtr + OFF_MIN1_VAL))
      (st4.mem (lPtr + OFF_MIN1_FIRST)) (st4.mem (lPtr + OFF_MIN1_LAST)) := by
    have he1 := h4_lt_hp0 (lPtr + OFF_MIN1_HAS) (hl_off_lt_hp OFF_MIN1_HAS (by decide))
      (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    have he2 := h4_lt_hp0 (lPtr + OFF_MIN1_VAL) (hl_off_lt_hp OFF_MIN1_VAL (by decide))
      (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    have he3 := h4_lt_hp0 (lPtr + OFF_MIN1_FIRST) (hl_off_lt_hp OFF_MIN1_FIRST (by decide))
      (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    have he4 := h4_lt_hp0 (lPtr + OFF_MIN1_LAST) (hl_off_lt_hp OFF_MIN1_LAST (by decide))
      (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    rw [he1, he2, he3, he4]
    have hc := canonicalNumAgg_of_node1 hpre.hl h0
    refine ⟨hc.1, fun hne => ⟨(hc.2 hne).1, numPtrOk_congr (le_trans hle1 hle2) hag40 (hc.2 hne).2⟩⟩
  have hx_ok1 : st4.mem (ptr + OFF_HASE) ≠ 0 →
      st4.mem (ptr + OFF_HASE) = 1 ∧ NumPtrOk st4.mem arenaHi hp2 h L (st4.mem (ptr + OFF_AF_PTR)) := by
    rw [h4_lt_hp0 (ptr + OFF_HASE) (hptr_off_lt_hp OFF_HASE (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)),
      h4_lt_hp0 (ptr + OFF_AF_PTR) (hptr_off_lt_hp OFF_AF_PTR (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
    intro hne
    have h1 := eq_one_of_le_one_ne_zero hpre.hhe hne
    exact ⟨h1, numPtrOk_congr (le_trans hle1 hle2) hag40 (hpre.he1 h1).2.1⟩
  have hr_ok1 : st4.mem (rPtr + OFF_MIN1_HAS) ≠ 0 →
      st4.mem (rPtr + OFF_MIN1_HAS) = 1 ∧ NumPtrOk st4.mem arenaHi hp2 h L (st4.mem (rPtr + OFF_MIN1_VAL)) := by
    have he1 := h4_lt_hp0 (rPtr + OFF_MIN1_HAS) (hr_off_lt_hp OFF_MIN1_HAS (by decide))
      (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
    have he2 := h4_lt_hp0 (rPtr + OFF_MIN1_VAL) (hr_off_lt_hp OFF_MIN1_VAL (by decide))
      (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
    rw [he1, he2]
    intro hne
    have hc := canonicalNumAgg_of_node1 hpre.hr h0
    exact ⟨(hc.2 hne).1, numPtrOk_congr (le_trans hle1 hle2) hag40 (hc.2 hne).2⟩
  rcases pullMinNumStmt_runs hp_ok (by omega) hx_arena hal_x hal_l hal_r
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      st4 h4_0 h4_1 h4_2 h4_4 h4_6 h4_15 h4_16 hl_ca1 hx_ok1 hr_ok1 with
    ⟨st5, c_m1, hr_m1, hc_m1, h5_0, h5_1, h5_2, h5_4, h5_6, h5_15, h5_16,
      hpres5, h5_m1h, h5_m1z, h5_m1nz, h5_m1f, h5_m1l⟩
  have h5_lt_hp0 : ∀ a < hp₀, a ≠ ptr + OFF_VCNT → a ≠ ptr + OFF_CSUM_FWD → a ≠ ptr + OFF_CSUM_BWD →
      a ≠ ptr + OFF_MIN1_HAS → a ≠ ptr + OFF_MIN1_VAL → a ≠ ptr + OFF_MIN1_FIRST →
      a ≠ ptr + OFF_MIN1_LAST → st5.mem a = mem₀ a := fun a ha h1 h2 h3 h4 h5 h6 h7 =>
    (hpres5 a h4 h5 h6 h7).trans (h4_lt_hp0 a ha h1 h2 h3)
  have hag50 : ∀ a, arenaHi ≤ a → a < hp₀ → st5.mem a = mem₀ a := fun a ha1 ha2 =>
    h5_lt_hp0 a ha2 (h_ar_ne a OFF_VCNT ha1 (by decide)) (h_ar_ne a OFF_CSUM_FWD ha1 (by decide))
      (h_ar_ne a OFF_CSUM_BWD ha1 (by decide)) (h_ar_ne a OFF_MIN1_HAS ha1 (by decide))
      (h_ar_ne a OFF_MIN1_VAL ha1 (by decide)) (h_ar_ne a OFF_MIN1_FIRST ha1 (by decide))
      (h_ar_ne a OFF_MIN1_LAST ha1 (by decide))
  have hl_ca2 : CanonicalNumAgg st5.mem arenaHi hp2 h L
      (st5.mem (lPtr + OFF_MIN2_HAS)) (st5.mem (lPtr + OFF_MIN2_VAL))
      (st5.mem (lPtr + OFF_MIN2_FIRST)) (st5.mem (lPtr + OFF_MIN2_LAST)) := by
    have he1 := h5_lt_hp0 (lPtr + OFF_MIN2_HAS) (hl_off_lt_hp OFF_MIN2_HAS (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    have he2 := h5_lt_hp0 (lPtr + OFF_MIN2_VAL) (hl_off_lt_hp OFF_MIN2_VAL (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    have he3 := h5_lt_hp0 (lPtr + OFF_MIN2_FIRST) (hl_off_lt_hp OFF_MIN2_FIRST (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    have he4 := h5_lt_hp0 (lPtr + OFF_MIN2_LAST) (hl_off_lt_hp OFF_MIN2_LAST (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
    rw [he1, he2, he3, he4]
    have hc := canonicalNumAgg_of_node2 hpre.hl h0
    refine ⟨hc.1, fun hne => ⟨(hc.2 hne).1, numPtrOk_congr (le_trans hle1 hle2) hag50 (hc.2 hne).2⟩⟩
  have hx_ok2 : st5.mem (ptr + OFF_HASE) ≠ 0 →
      st5.mem (ptr + OFF_HASE) = 1 ∧ NumPtrOk st5.mem arenaHi hp2 h L (st5.mem (ptr + OFF_AB_PTR)) := by
    rw [h5_lt_hp0 (ptr + OFF_HASE) (hptr_off_lt_hp OFF_HASE (by decide))
        (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))
        (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)),
      h5_lt_hp0 (ptr + OFF_AB_PTR) (hptr_off_lt_hp OFF_AB_PTR (by decide))
        (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))
        (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
    intro hne
    have h1 := eq_one_of_le_one_ne_zero hpre.hhe hne
    exact ⟨h1, numPtrOk_congr (le_trans hle1 hle2) hag50 (hpre.he1 h1).2.2.1⟩
  have hr_ok2 : st5.mem (rPtr + OFF_MIN2_HAS) ≠ 0 →
      st5.mem (rPtr + OFF_MIN2_HAS) = 1 ∧ NumPtrOk st5.mem arenaHi hp2 h L (st5.mem (rPtr + OFF_MIN2_VAL)) := by
    have he1 := h5_lt_hp0 (rPtr + OFF_MIN2_HAS) (hr_off_lt_hp OFF_MIN2_HAS (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
    have he2 := h5_lt_hp0 (rPtr + OFF_MIN2_VAL) (hr_off_lt_hp OFF_MIN2_VAL (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
    rw [he1, he2]
    intro hne
    have hc := canonicalNumAgg_of_node2 hpre.hr h0
    exact ⟨(hc.2 hne).1, numPtrOk_congr (le_trans hle1 hle2) hag50 (hc.2 hne).2⟩
  rcases pullMinNumStmt_runs hp_ok (by omega) hx_arena hal_x hal_l hal_r
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      st5 h5_0 h5_1 h5_2 h5_4 h5_6 h5_15 h5_16 hl_ca2 hx_ok2 hr_ok2 with
    ⟨st6, c_m2, hr_m2, hc_m2, h6_0, _, _, _, _, _, h6_16,
      hpres6, h6_m2h, h6_m2z, h6_m2nz, h6_m2f, h6_m2l⟩
  let st_hp : State := { st6 with mem := Function.update st6.mem (nodesBase - 1) hp2 }
  have hsub_hp : (Expr.bin .sub (.reg 0) (.const 1)).eval w st6 = some (nodesBase - 1) :=
    Expr.eval_sub (Expr.eval_reg_of_eq h6_0) (Expr.eval_const (by omega)) (by omega)
  have hstore_hp : Runs w p ω (Stmt.store (.bin .sub (.reg 0) (.const 1)) (.reg 16)) st6 .normal st_hp 5 :=
    runs_store_iff.mpr ⟨nodesBase - 1, hp2, hsub_hp, Expr.eval_reg_of_eq h6_16, rfl, rfl, rfl⟩
  have hret : Runs w p ω (Stmt.ret (.const 0)) st_hp (.returned 0) st_hp 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hbody : Runs w p ω
      (Stmt.assign 2 (nodePtrExpr 0 1) ;; Stmt.assign 3 (fieldLoadExpr 2 OFF_LEFT) ;;
       Stmt.assign 4 (nodePtrExpr 0 3) ;; Stmt.assign 5 (fieldLoadExpr 2 OFF_RIGHT) ;;
       Stmt.assign 6 (nodePtrExpr 0 5) ;;
       Stmt.assign 7 (.bin .add (.bin .add (fieldLoadExpr 4 OFF_VCNT) (fieldLoadExpr 2 OFF_ISV))
         (fieldLoadExpr 6 OFF_VCNT)) ;;
       Stmt.store (fieldAddrExpr 2 OFF_VCNT) (.reg 7) ;;
       Stmt.assign 15 (.load (.bin .sub (.reg 0) (.const 3))) ;;
       Stmt.assign 16 (.load (.bin .sub (.reg 0) (.const 1))) ;;
       Stmt.assign 7 (fieldLoadExpr 4 OFF_CSUM_FWD) ;; Stmt.assign 8 (fieldLoadExpr 2 OFF_COST_FWD) ;;
       addOptPtrStmt sp 7 8 15 16 18 ;;
       Stmt.assign 7 (fieldLoadExpr 6 OFF_CSUM_FWD) ;; addOptPtrStmt sp 18 7 15 16 8 ;;
       Stmt.store (fieldAddrExpr 2 OFF_CSUM_FWD) (.reg 8) ;;
       Stmt.assign 7 (fieldLoadExpr 4 OFF_CSUM_BWD) ;; Stmt.assign 8 (fieldLoadExpr 2 OFF_COST_BWD) ;;
       addOptPtrStmt sp 7 8 15 16 18 ;;
       Stmt.assign 7 (fieldLoadExpr 6 OFF_CSUM_BWD) ;; addOptPtrStmt sp 18 7 15 16 8 ;;
       Stmt.store (fieldAddrExpr 2 OFF_CSUM_BWD) (.reg 8) ;;
       pullMinNumStmt sp 1 2 4 6 OFF_AF_PTR OFF_MIN1_HAS OFF_MIN1_VAL OFF_MIN1_FIRST OFF_MIN1_LAST ;;
       pullMinNumStmt sp 1 2 4 6 OFF_AB_PTR OFF_MIN2_HAS OFF_MIN2_VAL OFF_MIN2_FIRST OFF_MIN2_LAST ;;
       Stmt.store (.bin .sub (.reg 0) (.const 1)) (.reg 16) ;;
       Stmt.ret (.const 0))
      st0 (.returned 0) st_hp
      (32 + (33 + (c_fwd + (c_bwd + (c_m1 + (c_m2 + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq5_normal hr_ptrs (runs_seq4_normal hr_vcnt
      (runs_seq6_normal hr_fwd (runs_seq6_normal hr_bwd
        (runs_seq_iff.mpr (Or.inr ⟨st5, c_m1, c_m2 + (5 + 2 + 1) + 1, hr_m1,
          runs_seq_iff.mpr (Or.inr ⟨st6, c_m2, 5 + 2 + 1, hr_m2,
            runs_seq_iff.mpr (Or.inr ⟨st_hp, 5, 2, hstore_hp, hret, rfl⟩), rfl⟩), rfl⟩)))))
  have hx_ne0 : x ≠ 0 := by omega
  have hfull : Runs w p ω (pullBody sp) st0 (.returned 0) st_hp
      (1 + (32 + (33 + (c_fwd + (c_bwd + (c_m1 + (c_m2 + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_cond_iff.mpr ⟨x, _, Expr.eval_reg_of_eq (rfl : st0.regs 1 = x),
      by simpa [pullBody, hx_ne0] using hbody, rfl⟩
  have hfin_hp : st_hp.mem (nodesBase - 1) = hp2 := by dsimp [st_hp]; exact Function.update_self _ _ _
  have hfin_ne_nb1 : ∀ addr, addr ≠ nodesBase - 1 → st_hp.mem addr = st6.mem addr := fun _ h =>
    Function.update_of_ne h _ _
  have hfin_out : ∀ addr, addr ≠ nodesBase - 1 → (addr < ptr ∨ ptr + NODE_STRIDE ≤ addr) →
      addr < hp₀ → st_hp.mem addr = mem₀ addr := fun addr hne hout hlt => by
    rw [hfin_ne_nb1 addr hne,
      hpres6 addr (addr_ne_of_outside_slot hout (by decide)) (addr_ne_of_outside_slot hout (by decide))
        (addr_ne_of_outside_slot hout (by decide)) (addr_ne_of_outside_slot hout (by decide))]
    exact h5_lt_hp0 addr hlt (addr_ne_of_outside_slot hout (by decide))
      (addr_ne_of_outside_slot hout (by decide)) (addr_ne_of_outside_slot hout (by decide))
      (addr_ne_of_outside_slot hout (by decide)) (addr_ne_of_outside_slot hout (by decide))
      (addr_ne_of_outside_slot hout (by decide)) (addr_ne_of_outside_slot hout (by decide))
  have hag_fin : ∀ a, arenaHi ≤ a → a < hp2 → st_hp.mem a = st6.mem a := fun a ha _ =>
    hfin_ne_nb1 a (hnb1_ne_ar a ha)
  have hfin_hz : ZeroFrom st_hp.mem hp2 := fun a ha => by
    have ha_ar : arenaHi ≤ a := le_trans harena (le_trans (le_trans hle1 hle2) ha)
    rw [hfin_ne_nb1 a (hnb1_ne_ar a ha_ar),
      hpres6 a (h_ar_ne a _ ha_ar (by decide)) (h_ar_ne a _ ha_ar (by decide))
        (h_ar_ne a _ ha_ar (by decide)) (h_ar_ne a _ ha_ar (by decide)),
      hpres5 a (h_ar_ne a _ ha_ar (by decide)) (h_ar_ne a _ ha_ar (by decide))
        (h_ar_ne a _ ha_ar (by decide)) (h_ar_ne a _ ha_ar (by decide))]
    exact hz4 a ha
  have hfin_static : ∀ off < NODE_STRIDE,
      off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
      off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
      nodeField st_hp.mem nodesBase x off = nodeField mem₀ nodesBase x off := by
    intro off hoff hv hcf hcb h1h h1v h1f h1l h2h h2v h2f h2l
    change st_hp.mem (ptr + off) = mem₀ (ptr + off)
    rw [hfin_ne_nb1 (ptr + off) (hnb1_ne_slot off).symm,
      hpres6 (ptr + off) (h_slot_ne h2h) (h_slot_ne h2v) (h_slot_ne h2f) (h_slot_ne h2l)]
    exact h5_lt_hp0 (ptr + off) (hptr_off_lt_hp off hoff)
      (h_slot_ne hv) (h_slot_ne hcf) (h_slot_ne hcb)
      (h_slot_ne h1h) (h_slot_ne h1v) (h_slot_ne h1f) (h_slot_ne h1l)
  have hag_hp0 : ∀ a, arenaHi ≤ a → a < hp₀ → st_hp.mem a = mem₀ a := fun a ha1 ha2 =>
    hfin_out a (hnb1_ne_ar a ha1) (Or.inr (le_trans hx_arena ha1)) ha2
  have hsub_agree : ∀ {tSub : AuxTree} {parSub ppSub : ℕ},
      TreeMemMatch w h L mem₀ nodesBase cap tSub parSub ppSub →
      x ∉ tSub.toList →
      ∀ u ∈ tSub.toList, ∀ off < NODE_STRIDE,
        nodeField st_hp.mem nodesBase u off = nodeField mem₀ nodesBase u off := by
    intro tSub parSub ppSub htSub hx_nin u hu off hoff
    have hu_b := (htSub.nodup_perm_mem hu).1
    have hu_le := (htSub.nodup_perm_mem hu).2
    have hux : u ≠ x := fun h => by subst h; exact hx_nin hu
    change st_hp.mem (nodesBase + NODE_STRIDE * u + off) =
      mem₀ (nodesBase + NODE_STRIDE * u + off)
    exact hfin_out _ (slot_addr_ne_nb1 hnb hu_b) (slot_addr_disj_of_ne hux hoff)
      (lt_of_lt_of_le (slot_addr_lt_arenaHi hu_le hoff) harena)
  have hl_agree : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
      nodeField st_hp.mem nodesBase u off = nodeField mem₀ nodesBase u off :=
    hsub_agree hpre.hl hx_nin_l
  have hr_agree : ∀ u ∈ r.toList, ∀ off < NODE_STRIDE,
      nodeField st_hp.mem nodesBase u off = nodeField mem₀ nodesBase u off :=
    hsub_agree hpre.hr hx_nin_r
  have hfin_l : TreeMemMatch w h L st_hp.mem nodesBase cap l x 0 :=
    memAgree_treeMemMatch_of_nodeList hpre.hl hl_agree (by rw [hfin_hp]; exact le_trans hle1 hle2) hag_hp0
  have hfin_r : TreeMemMatch w h L st_hp.mem nodesBase cap r x 0 :=
    memAgree_treeMemMatch_of_nodeList hpre.hr hr_agree (by rw [hfin_hp]; exact le_trans hle1 hle2) hag_hp0
  have hfin_vcnt : nodeField st_hp.mem nodesBase x OFF_VCNT = listVcnt mem₀ nodesBase seq := by
    change st_hp.mem (ptr + OFF_VCNT) = listVcnt mem₀ nodesBase seq
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm,
      hpres6 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)),
      hpres5 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)),
      hpres4 _ (lt_of_lt_of_le (hptr_off_lt_hp _ (by decide)) hle1) (h_slot_ne (by decide)),
      hpres3 _ (hptr_off_lt_hp _ (by decide)) (h_slot_ne (by decide)), hm2]
    exact Function.update_self _ _ _
  have hag_fin_st3 : ∀ a, arenaHi ≤ a → a < hp1 → st_hp.mem a = st3.mem a := fun a ha1 ha2 => by
    rw [hfin_ne_nb1 a (hnb1_ne_ar a ha1),
      hpres6 a (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))
        (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide)),
      hpres5 a (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))
        (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))]
    exact hpres4 a ha2 (h_ar_ne a _ ha1 (by decide))
  have hfin_cf_ptr : st_hp.mem (ptr + OFF_CSUM_FWD) = st3.mem (ptr + OFF_CSUM_FWD) := by
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm,
      hpres6 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)),
      hpres5 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)),
      hpres4 _ (lt_of_lt_of_le (hptr_off_lt_hp _ (by decide)) hle1) (h_slot_ne (by decide))]
  have hfin_cf_ok : OptNumPtrOk st_hp.mem arenaHi hp2 h L (nodeField st_hp.mem nodesBase x OFF_CSUM_FWD) := by
    change OptNumPtrOk st_hp.mem arenaHi hp2 h L (st_hp.mem (ptr + OFF_CSUM_FWD))
    rw [hfin_cf_ptr]
    exact optNumPtrOk_congr hle2 hag_fin_st3 h3_cf_ok
  have hag_fin_st4 : ∀ a, arenaHi ≤ a → a < hp2 → st_hp.mem a = st4.mem a := fun a ha1 ha2 => by
    rw [hfin_ne_nb1 a (hnb1_ne_ar a ha1),
      hpres6 a (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))
        (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide)),
      hpres5 a (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))
        (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))]
  have hfin_cb_ptr : st_hp.mem (ptr + OFF_CSUM_BWD) = st4.mem (ptr + OFF_CSUM_BWD) := by
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm,
      hpres6 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)),
      hpres5 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
  have hfin_cb_ok : OptNumPtrOk st_hp.mem arenaHi hp2 h L (nodeField st_hp.mem nodesBase x OFF_CSUM_BWD) := by
    change OptNumPtrOk st_hp.mem arenaHi hp2 h L (st_hp.mem (ptr + OFF_CSUM_BWD))
    rw [hfin_cb_ptr]
    exact optNumPtrOk_congr le_rfl hag_fin_st4 h4_cb_ok
  have hfin_cf_val : optIntVal st_hp.mem h L (nodeField st_hp.mem nodesBase x OFF_CSUM_FWD) =
      wrap h L (listRawCost (evalMemSteps mem₀ nodesBase h L (.node x l r) false 0)) := by
    change optIntVal st_hp.mem h L (st_hp.mem (ptr + OFF_CSUM_FWD)) = _
    rw [hfin_cf_ptr, optIntVal_agree_heap hag_fin_st3 h3_cf_ok, h3_cf_val]
    have h2_lcf : optIntVal st2.mem h L (st2.mem (lPtr + OFF_CSUM_FWD)) =
        wrap h L (listRawCost (evalMemSteps mem₀ nodesBase h L l false 0)) := by
      rw [h2_other _ (hdisj_l _ (by decide) _ (by decide)).symm]
      change optIntVal st2.mem h L (nodeField mem₀ nodesBase l.rootId OFF_CSUM_FWD) = _
      rw [optIntVal_agree_heap hag20 hl_cf_ok]
      exact (hpre.hl.rootAggs h0).2.1
    have h2_xcf : optIntVal st2.mem h L (st2.mem (ptr + OFF_COST_FWD)) =
        wrap h L (listRawCost ((nodeOwnRawStep mem₀ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList) := by
      rw [h2_other _ (h_slot_ne (by decide))]
      change optIntVal st2.mem h L (nodeField mem₀ nodesBase x OFF_COST_FWD) = _
      rw [optIntVal_agree_heap hag20 hx_cf_ok]
      exact (listRawCost_own_eq_fwd (_w := w) hpre.hhe hpre.he1 (fun he =>
        ⟨(hpre.he0 he).2.2.2.2.1, (hpre.he0 he).2.2.2.2.2⟩)).1.symm
    have h2_rcf : optIntVal st2.mem h L (st2.mem (rPtr + OFF_CSUM_FWD)) =
        wrap h L (listRawCost (evalMemSteps mem₀ nodesBase h L r false 0)) := by
      rw [h2_other _ (hdisj_r _ (by decide) _ (by decide)).symm]
      change optIntVal st2.mem h L (nodeField mem₀ nodesBase r.rootId OFF_CSUM_FWD) = _
      rw [optIntVal_agree_heap hag20 hr_cf_ok]
      exact (hpre.hr.rootAggs h0).2.1
    have hrev_f : revFlag mem₀ nodesBase x = false := by simp [revFlag, hpre.hrev0]
    have htag0 : nodeTagInt mem₀ nodesBase h L x = 0 := by
      simp [nodeTagInt, hpre.htp0, optIntVal]
    rw [h2_lcf, h2_xcf, h2_rcf, wrap_add3]
    simp only [evalMemSteps, hrev_f, htag0, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, add_zero,
      listRawCost_append]
  have hfin_cb_val : optIntVal st_hp.mem h L (nodeField st_hp.mem nodesBase x OFF_CSUM_BWD) =
      wrap h L (-listRawCost (evalMemSteps mem₀ nodesBase h L (.node x l r) false 0)) := by
    change optIntVal st_hp.mem h L (st_hp.mem (ptr + OFF_CSUM_BWD)) = _
    rw [hfin_cb_ptr, optIntVal_agree_heap hag_fin_st4 h4_cb_ok, h4_cb_val]
    have h3_lcb : optIntVal st3.mem h L (st3.mem (lPtr + OFF_CSUM_BWD)) =
        wrap h L (-listRawCost (evalMemSteps mem₀ nodesBase h L l false 0)) := by
      rw [h3_lt_hp0 _ (hl_off_lt_hp _ (by decide))
        (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm]
      change optIntVal st3.mem h L (nodeField mem₀ nodesBase l.rootId OFF_CSUM_BWD) = _
      rw [optIntVal_agree_heap hag30 hl_cb_ok]
      exact (hpre.hl.rootAggs h0).2.2.1
    have h3_xcb : optIntVal st3.mem h L (st3.mem (ptr + OFF_COST_BWD)) =
        wrap h L (-listRawCost ((nodeOwnRawStep mem₀ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList) := by
      rw [h3_lt_hp0 _ (hptr_off_lt_hp _ (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
      change optIntVal st3.mem h L (nodeField mem₀ nodesBase x OFF_COST_BWD) = _
      rw [optIntVal_agree_heap hag30 hx_cb_ok]
      exact (listRawCost_own_eq_fwd (_w := w) hpre.hhe hpre.he1 (fun he =>
        ⟨(hpre.he0 he).2.2.2.2.1, (hpre.he0 he).2.2.2.2.2⟩)).2.symm
    have h3_rcb : optIntVal st3.mem h L (st3.mem (rPtr + OFF_CSUM_BWD)) =
        wrap h L (-listRawCost (evalMemSteps mem₀ nodesBase h L r false 0)) := by
      rw [h3_lt_hp0 _ (hr_off_lt_hp _ (by decide))
        (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm]
      change optIntVal st3.mem h L (nodeField mem₀ nodesBase r.rootId OFF_CSUM_BWD) = _
      rw [optIntVal_agree_heap hag30 hr_cb_ok]
      exact (hpre.hr.rootAggs h0).2.2.1
    have hrev_f : revFlag mem₀ nodesBase x = false := by simp [revFlag, hpre.hrev0]
    have htag0 : nodeTagInt mem₀ nodesBase h L x = 0 := by
      simp [nodeTagInt, hpre.htp0, optIntVal]
    rw [h3_lcb, h3_xcb, h3_rcb, wrap_neg3]
    simp only [evalMemSteps, hrev_f, htag0, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, add_zero,
      listRawCost_append]
  let steps := evalMemSteps mem₀ nodesBase h L (.node x l r) false 0
  have hsteps_split : steps =
      evalMemSteps mem₀ nodesBase h L l false 0 ++
      ((nodeOwnRawStep mem₀ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList ++
      evalMemSteps mem₀ nodesBase h L r false 0 := by
    have hrev_f : revFlag mem₀ nodesBase x = false := by simp [revFlag, hpre.hrev0]
    have htag0 : nodeTagInt mem₀ nodesBase h L x = 0 := by
      simp [nodeTagInt, hpre.htp0, optIntVal]
    simp only [steps, evalMemSteps, hrev_f, htag0, Bool.false_xor, Bool.false_eq_true, ↓reduceIte, add_zero]
  let agg1_tgt := listIntMinAgg (steps.map fun s => (s.nodeId, s.dirAvail))
  let agg2_tgt := listIntMinAgg (steps.map fun s => (s.nodeId, s.flip.dirAvail))
  have hagg1_eq : combineIntMinAgg
      (combineIntMinAgg
        (decodeNumAgg st4.mem h L (st4.mem (lPtr + OFF_MIN1_HAS)) (st4.mem (lPtr + OFF_MIN1_VAL))
          (st4.mem (lPtr + OFF_MIN1_FIRST)) (st4.mem (lPtr + OFF_MIN1_LAST)))
        (decodeNumAgg st4.mem h L (st4.mem (ptr + OFF_HASE)) (st4.mem (ptr + OFF_AF_PTR)) x x))
      (decodeNumAgg st4.mem h L (st4.mem (rPtr + OFF_MIN1_HAS)) (st4.mem (rPtr + OFF_MIN1_VAL))
        (st4.mem (rPtr + OFF_MIN1_FIRST)) (st4.mem (rPtr + OFF_MIN1_LAST))) = agg1_tgt := by
    have hl1 : decodeNumAgg st4.mem h L (st4.mem (lPtr + OFF_MIN1_HAS)) (st4.mem (lPtr + OFF_MIN1_VAL))
        (st4.mem (lPtr + OFF_MIN1_FIRST)) (st4.mem (lPtr + OFF_MIN1_LAST)) =
        listIntMinAgg ((evalMemSteps mem₀ nodesBase h L l false 0).map fun s => (s.nodeId, s.dirAvail)) := by
      have he1 := h4_lt_hp0 (lPtr + OFF_MIN1_HAS) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have he2 := h4_lt_hp0 (lPtr + OFF_MIN1_VAL) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have he3 := h4_lt_hp0 (lPtr + OFF_MIN1_FIRST) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have he4 := h4_lt_hp0 (lPtr + OFF_MIN1_LAST) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have hk : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase l.rootId OFF_MIN1_VAL) := by
        have hc := canonicalNumAgg_of_node1 hpre.hl h0
        by_cases hnz : nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS = 0
        · exact Or.inl (hc.1 hnz).1
        · exact Or.inr ⟨(hc.2 hnz).2.2.1, (hc.2 hnz).2.2.2.1, (hc.2 hnz).2.2.2.2⟩
      rw [he1, he2, he3, he4]
      change decodeNumAgg st4.mem h L (nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS)
          (nodeField mem₀ nodesBase l.rootId OFF_MIN1_VAL)
          (nodeField mem₀ nodesBase l.rootId OFF_MIN1_FIRST)
          (nodeField mem₀ nodesBase l.rootId OFF_MIN1_LAST) = _
      simp only [decodeNumAgg, optIntVal_agree_heap hag40 hk]
      exact (hpre.hl.rootAggs h0).2.2.2.1
    have hr1 : decodeNumAgg st4.mem h L (st4.mem (rPtr + OFF_MIN1_HAS)) (st4.mem (rPtr + OFF_MIN1_VAL))
        (st4.mem (rPtr + OFF_MIN1_FIRST)) (st4.mem (rPtr + OFF_MIN1_LAST)) =
        listIntMinAgg ((evalMemSteps mem₀ nodesBase h L r false 0).map fun s => (s.nodeId, s.dirAvail)) := by
      have he1 := h4_lt_hp0 (rPtr + OFF_MIN1_HAS) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have he2 := h4_lt_hp0 (rPtr + OFF_MIN1_VAL) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have he3 := h4_lt_hp0 (rPtr + OFF_MIN1_FIRST) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have he4 := h4_lt_hp0 (rPtr + OFF_MIN1_LAST) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have hk : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase r.rootId OFF_MIN1_VAL) := by
        have hc := canonicalNumAgg_of_node1 hpre.hr h0
        by_cases hnz : nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS = 0
        · exact Or.inl (hc.1 hnz).1
        · exact Or.inr ⟨(hc.2 hnz).2.2.1, (hc.2 hnz).2.2.2.1, (hc.2 hnz).2.2.2.2⟩
      rw [he1, he2, he3, he4]
      change decodeNumAgg st4.mem h L (nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS)
          (nodeField mem₀ nodesBase r.rootId OFF_MIN1_VAL)
          (nodeField mem₀ nodesBase r.rootId OFF_MIN1_FIRST)
          (nodeField mem₀ nodesBase r.rootId OFF_MIN1_LAST) = _
      simp only [decodeNumAgg, optIntVal_agree_heap hag40 hk]
      exact (hpre.hr.rootAggs h0).2.2.2.1
    have hown1 := (listIntMinAgg_own_eq (x := x) (cap := cap) hpre.hhe
      (fun he => ⟨(hpre.he1 he).1, (hpre.he1 he).2.1, (hpre.he1 he).2.2.1⟩)
      (fun he => ⟨(hpre.he0 he).2.2.1, (hpre.he0 he).2.2.2.1⟩)).1
    have hx_he : st4.mem (ptr + OFF_HASE) = nodeField mem₀ nodesBase x OFF_HASE :=
      h4_lt_hp0 (ptr + OFF_HASE) (hptr_off_lt_hp _ (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))
    have hx_af : st4.mem (ptr + OFF_AF_PTR) = nodeField mem₀ nodesBase x OFF_AF_PTR :=
      h4_lt_hp0 (ptr + OFF_AF_PTR) (hptr_off_lt_hp _ (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))
    have hox : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase x OFF_AF_PTR) := by
      by_cases he : nodeField mem₀ nodesBase x OFF_HASE = 0
      · exact Or.inl (hpre.he0 he).2.2.1
      · have h1 := eq_one_of_le_one_ne_zero hpre.hhe he
        have hk := (hpre.he1 h1).2.1
        exact Or.inr ⟨hk.2.1, hk.2.2.1, hk.2.2.2⟩
    have hm1_comb : combineIntMinAgg
        (listIntMinAgg ((evalMemSteps mem₀ nodesBase h L l false 0).map fun s => (s.nodeId, s.dirAvail)))
        (decodeNumAgg st4.mem h L (st4.mem (ptr + OFF_HASE)) (st4.mem (ptr + OFF_AF_PTR)) x x) =
        combineIntMinAgg
          (listIntMinAgg ((evalMemSteps mem₀ nodesBase h L l false 0).map fun s => (s.nodeId, s.dirAvail)))
          (listIntMinAgg (((nodeOwnRawStep mem₀ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList.map
            fun s => (s.nodeId, s.dirAvail))) := by
      rw [hown1]
      simp only [decodeNumAgg, hx_he, hx_af, optIntVal_agree_heap hag40 hox]
      by_cases he : nodeField mem₀ nodesBase x OFF_HASE = 0
      · have hdec : decide ((0 : ℕ) ≠ 0) = false := rfl
        rw [he, hdec]
        simp only [↓reduceIte]
        exact combineIntMinAgg_own_zero_eq listIntMinAgg_false_eq
      · simp [he]
    rw [hl1, hm1_comb, hr1]
    simp only [agg1_tgt, hsteps_split, listIntMinAgg_append_map]
  have hagg2_eq : combineIntMinAgg
      (combineIntMinAgg
        (decodeNumAgg st5.mem h L (st5.mem (lPtr + OFF_MIN2_HAS)) (st5.mem (lPtr + OFF_MIN2_VAL))
          (st5.mem (lPtr + OFF_MIN2_FIRST)) (st5.mem (lPtr + OFF_MIN2_LAST)))
        (decodeNumAgg st5.mem h L (st5.mem (ptr + OFF_HASE)) (st5.mem (ptr + OFF_AB_PTR)) x x))
      (decodeNumAgg st5.mem h L (st5.mem (rPtr + OFF_MIN2_HAS)) (st5.mem (rPtr + OFF_MIN2_VAL))
        (st5.mem (rPtr + OFF_MIN2_FIRST)) (st5.mem (rPtr + OFF_MIN2_LAST))) = agg2_tgt := by
    have hl2 : decodeNumAgg st5.mem h L (st5.mem (lPtr + OFF_MIN2_HAS)) (st5.mem (lPtr + OFF_MIN2_VAL))
        (st5.mem (lPtr + OFF_MIN2_FIRST)) (st5.mem (lPtr + OFF_MIN2_LAST)) =
        listIntMinAgg ((evalMemSteps mem₀ nodesBase h L l false 0).map fun s => (s.nodeId, s.flip.dirAvail)) := by
      have he1 := h5_lt_hp0 (lPtr + OFF_MIN2_HAS) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have he2 := h5_lt_hp0 (lPtr + OFF_MIN2_VAL) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have he3 := h5_lt_hp0 (lPtr + OFF_MIN2_FIRST) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have he4 := h5_lt_hp0 (lPtr + OFF_MIN2_LAST) (hl_off_lt_hp _ (by decide)) (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm (hdisj_l _ (by decide) _ (by decide)).symm
      have hk : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase l.rootId OFF_MIN2_VAL) := by
        have hc := canonicalNumAgg_of_node2 hpre.hl h0
        by_cases hnz : nodeField mem₀ nodesBase l.rootId OFF_MIN2_HAS = 0
        · exact Or.inl (hc.1 hnz).1
        · exact Or.inr ⟨(hc.2 hnz).2.2.1, (hc.2 hnz).2.2.2.1, (hc.2 hnz).2.2.2.2⟩
      rw [he1, he2, he3, he4]
      change decodeNumAgg st5.mem h L (nodeField mem₀ nodesBase l.rootId OFF_MIN2_HAS)
          (nodeField mem₀ nodesBase l.rootId OFF_MIN2_VAL)
          (nodeField mem₀ nodesBase l.rootId OFF_MIN2_FIRST)
          (nodeField mem₀ nodesBase l.rootId OFF_MIN2_LAST) = _
      simp only [decodeNumAgg, optIntVal_agree_heap hag50 hk]
      exact (hpre.hl.rootAggs h0).2.2.2.2
    have hr2 : decodeNumAgg st5.mem h L (st5.mem (rPtr + OFF_MIN2_HAS)) (st5.mem (rPtr + OFF_MIN2_VAL))
        (st5.mem (rPtr + OFF_MIN2_FIRST)) (st5.mem (rPtr + OFF_MIN2_LAST)) =
        listIntMinAgg ((evalMemSteps mem₀ nodesBase h L r false 0).map fun s => (s.nodeId, s.flip.dirAvail)) := by
      have he1 := h5_lt_hp0 (rPtr + OFF_MIN2_HAS) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have he2 := h5_lt_hp0 (rPtr + OFF_MIN2_VAL) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have he3 := h5_lt_hp0 (rPtr + OFF_MIN2_FIRST) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have he4 := h5_lt_hp0 (rPtr + OFF_MIN2_LAST) (hr_off_lt_hp _ (by decide)) (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm (hdisj_r _ (by decide) _ (by decide)).symm
      have hk : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase r.rootId OFF_MIN2_VAL) := by
        have hc := canonicalNumAgg_of_node2 hpre.hr h0
        by_cases hnz : nodeField mem₀ nodesBase r.rootId OFF_MIN2_HAS = 0
        · exact Or.inl (hc.1 hnz).1
        · exact Or.inr ⟨(hc.2 hnz).2.2.1, (hc.2 hnz).2.2.2.1, (hc.2 hnz).2.2.2.2⟩
      rw [he1, he2, he3, he4]
      change decodeNumAgg st5.mem h L (nodeField mem₀ nodesBase r.rootId OFF_MIN2_HAS)
          (nodeField mem₀ nodesBase r.rootId OFF_MIN2_VAL)
          (nodeField mem₀ nodesBase r.rootId OFF_MIN2_FIRST)
          (nodeField mem₀ nodesBase r.rootId OFF_MIN2_LAST) = _
      simp only [decodeNumAgg, optIntVal_agree_heap hag50 hk]
      exact (hpre.hr.rootAggs h0).2.2.2.2
    have hown2 := (listIntMinAgg_own_eq (x := x) (cap := cap) hpre.hhe
      (fun he => ⟨(hpre.he1 he).1, (hpre.he1 he).2.1, (hpre.he1 he).2.2.1⟩)
      (fun he => ⟨(hpre.he0 he).2.2.1, (hpre.he0 he).2.2.2.1⟩)).2
    have hx_he : st5.mem (ptr + OFF_HASE) = nodeField mem₀ nodesBase x OFF_HASE :=
      h5_lt_hp0 (ptr + OFF_HASE) (hptr_off_lt_hp _ (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))
    have hx_ab : st5.mem (ptr + OFF_AB_PTR) = nodeField mem₀ nodesBase x OFF_AB_PTR :=
      h5_lt_hp0 (ptr + OFF_AB_PTR) (hptr_off_lt_hp _ (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))
    have hox : OptNumPtrOk mem₀ arenaHi hp₀ h L (nodeField mem₀ nodesBase x OFF_AB_PTR) := by
      by_cases he : nodeField mem₀ nodesBase x OFF_HASE = 0
      · exact Or.inl (hpre.he0 he).2.2.2.1
      · have h1 := eq_one_of_le_one_ne_zero hpre.hhe he
        have hk := (hpre.he1 h1).2.2.1
        exact Or.inr ⟨hk.2.1, hk.2.2.1, hk.2.2.2⟩
    have hm2_comb : combineIntMinAgg
        (listIntMinAgg ((evalMemSteps mem₀ nodesBase h L l false 0).map fun s => (s.nodeId, s.flip.dirAvail)))
        (decodeNumAgg st5.mem h L (st5.mem (ptr + OFF_HASE)) (st5.mem (ptr + OFF_AB_PTR)) x x) =
        combineIntMinAgg
          (listIntMinAgg ((evalMemSteps mem₀ nodesBase h L l false 0).map fun s => (s.nodeId, s.flip.dirAvail)))
          (listIntMinAgg (((nodeOwnRawStep mem₀ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList.map
            fun s => (s.nodeId, s.flip.dirAvail))) := by
      rw [hown2]
      simp only [decodeNumAgg, hx_he, hx_ab, optIntVal_agree_heap hag50 hox]
      by_cases he : nodeField mem₀ nodesBase x OFF_HASE = 0
      · have hdec : decide ((0 : ℕ) ≠ 0) = false := rfl
        rw [he, hdec]
        simp only [↓reduceIte]
        exact combineIntMinAgg_own_zero_eq listIntMinAgg_false_eq
      · simp [he]
    rw [hl2, hm2_comb, hr2]
    simp only [agg2_tgt, hsteps_split, listIntMinAgg_append_map]
  rw [hagg1_eq] at h5_m1h h5_m1nz h5_m1f h5_m1l
  rw [hagg2_eq] at h6_m2h h6_m2nz h6_m2f h6_m2l
  have hfin_m1h : nodeField st_hp.mem nodesBase x OFF_MIN1_HAS = if agg1_tgt.has then 1 else 0 := by
    change st_hp.mem (ptr + OFF_MIN1_HAS) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm,
      hpres6 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
    exact h5_m1h
  have hfin_m1v : nodeField st_hp.mem nodesBase x OFF_MIN1_VAL = st5.mem (ptr + OFF_MIN1_VAL) := by
    change st_hp.mem (ptr + OFF_MIN1_VAL) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm,
      hpres6 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
  have hfin_m1f : nodeField st_hp.mem nodesBase x OFF_MIN1_FIRST = agg1_tgt.first := by
    change st_hp.mem (ptr + OFF_MIN1_FIRST) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm,
      hpres6 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
    exact h5_m1f
  have hfin_m1l : nodeField st_hp.mem nodesBase x OFF_MIN1_LAST = agg1_tgt.last := by
    change st_hp.mem (ptr + OFF_MIN1_LAST) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm,
      hpres6 _ (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide)) (h_slot_ne (by decide))]
    exact h5_m1l
  have hfin_m2h : nodeField st_hp.mem nodesBase x OFF_MIN2_HAS = if agg2_tgt.has then 1 else 0 := by
    change st_hp.mem (ptr + OFF_MIN2_HAS) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm]
    exact h6_m2h
  have hfin_m2v : nodeField st_hp.mem nodesBase x OFF_MIN2_VAL = st6.mem (ptr + OFF_MIN2_VAL) := by
    change st_hp.mem (ptr + OFF_MIN2_VAL) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm]
  have hfin_m2f : nodeField st_hp.mem nodesBase x OFF_MIN2_FIRST = agg2_tgt.first := by
    change st_hp.mem (ptr + OFF_MIN2_FIRST) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm]
    exact h6_m2f
  have hfin_m2l : nodeField st_hp.mem nodesBase x OFF_MIN2_LAST = agg2_tgt.last := by
    change st_hp.mem (ptr + OFF_MIN2_LAST) = _
    rw [hfin_ne_nb1 _ (hnb1_ne_slot _).symm]
    exact h6_m2l
  have hag_fin_st5 : ∀ a, arenaHi ≤ a → a < hp2 → st_hp.mem a = st5.mem a := fun a ha1 ha2 => by
    rw [hfin_ne_nb1 a (hnb1_ne_ar a ha1)]
    exact hpres6 a (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))
      (h_ar_ne a _ ha1 (by decide)) (h_ar_ne a _ ha1 (by decide))
  have hhas_iff1 : agg1_tgt.has = true ↔ steps ≠ [] := by
    rw [listIntMinAgg_has_iff_ne_nil]; simp
  have hhas_iff2 : agg2_tgt.has = true ↔ steps ≠ [] := by
    rw [listIntMinAgg_has_iff_ne_nil]; simp
  have hhas_bool : agg2_tgt.has = agg1_tgt.has := Bool.eq_iff_iff.mpr (by rw [hhas_iff1, hhas_iff2])
  have hsteps_fin : evalMemSteps st_hp.mem nodesBase h L (.node x l r) false 0 = steps := by
    have hrev_f' : revFlag st_hp.mem nodesBase x = false := by
      simp [revFlag, hfin_static OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.hrev0]
    have htag0' : nodeTagInt st_hp.mem nodesBase h L x = 0 := by
      simp [nodeTagInt, hfin_static OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.htp0, optIntVal]
    have hown_eq : nodeOwnRawStep st_hp.mem nodesBase h L x = nodeOwnRawStep mem₀ nodesBase h L x := by
      have hhe := hfin_static OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      by_cases he : nodeField mem₀ nodesBase x OFF_HASE = 0
      · simp [nodeOwnRawStep, hhe, he]
      · have h1 := eq_one_of_le_one_ne_zero hpre.hhe he
        have hk := hpre.he1 h1
        have hdir := hfin_static OFF_DIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have heid := hfin_static OFF_EID (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have heu := hfin_static OFF_EU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hev := hfin_static OFF_EV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hcf := hfin_static OFF_COST_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hcb := hfin_static OFF_COST_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have haf := hfin_static OFF_AF_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hab := hfin_static OFF_AB_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hfl := hfin_static OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        simp only [nodeOwnRawStep, hhe, he, ↓reduceIte, hdir, heid, heu, hev, hcf, hcb, haf, hab, hfl,
          intVal_agree_heap hag_hp0 hk.1.2.1 hk.1.2.2.1,
          intVal_agree_heap hag_hp0 hk.2.1.2.1 hk.2.1.2.2.1,
          intVal_agree_heap hag_hp0 hk.2.2.1.2.1 hk.2.2.1.2.2.1,
          intVal_agree_heap hag_hp0 hk.2.2.2.1.2.1 hk.2.2.2.1.2.2.1,
          intVal_agree_heap hag_hp0 hk.2.2.2.2.1.2.1 hk.2.2.2.2.1.2.2.1]
    rw [hsteps_split]
    simp only [evalMemSteps, hrev_f', htag0', Bool.false_xor, Bool.false_eq_true, ↓reduceIte, add_zero, hown_eq]
    rw [evalMemSteps_agree hpre.hl hl_agree hag_hp0 false 0,
      evalMemSteps_agree hpre.hr hr_agree hag_hp0 false 0]
  have htree : TreeMemMatch w h L st_hp.mem nodesBase cap (.node x l r) parId pp := by
    refine ⟨hx1, hx2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfin_l, hfin_r⟩
    · rw [hfin_static OFF_LEFT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hL
    · rw [hfin_static OFF_RIGHT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hR
    · rw [hfin_static OFF_PARENT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hP
    · rw [hfin_static OFF_PPAR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hPP
    · rw [hfin_static OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.hrev0]; omega
    · rw [hfin_static OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hiv
    · rw [hfin_static OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hhe
    · rw [hfin_static OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hsum
    · rw [hfin_static OFF_DIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hdir
    · rw [hfin_static OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.hht0]; omega
    · rw [hfin_static OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.htn0]; omega
    · rw [hfin_static OFF_EU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.heu
    · rw [hfin_static OFF_EV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.hev
    · rw [hfin_static OFF_EID (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hpre.heid
    · rw [hfin_static OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_AF_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_AB_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_COST_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_COST_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      intro h1
      obtain ⟨kf, kaf, kab, kcf, kcb, hcb⟩ := hpre.he1 h1
      rw [hfin_hp]
      refine ⟨numPtrOk_congr (le_trans hle1 hle2) hag_hp0 kf,
        numPtrOk_congr (le_trans hle1 hle2) hag_hp0 kaf,
        numPtrOk_congr (le_trans hle1 hle2) hag_hp0 kab,
        numPtrOk_congr (le_trans hle1 hle2) hag_hp0 kcf,
        numPtrOk_congr (le_trans hle1 hle2) hag_hp0 kcb, ?_⟩
      rw [intVal_agree_heap hag_hp0 kcb.2.1 kcb.2.2.1, intVal_agree_heap hag_hp0 kcf.2.1 kcf.2.2.1]
      exact hcb
    · rw [hfin_static OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_DIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_AF_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_AB_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_COST_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_COST_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hpre.he0
    · change OptNumPtrOk st_hp.mem arenaHi (st_hp.mem (nodesBase - 1)) h L _
      rw [hfin_hp]; exact hfin_cf_ok
    · change OptNumPtrOk st_hp.mem arenaHi (st_hp.mem (nodesBase - 1)) h L _
      rw [hfin_hp]; exact hfin_cb_ok
    · rw [hfin_static OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.hht0]
      intro h1; cases h1
    · rw [hfin_static OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hfin_static OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact fun _ => ⟨hpre.htp0, hpre.htn0⟩
    · rw [hfin_m1h]; split_ifs <;> omega
    · rw [hfin_m2h, hfin_m1h, hhas_bool]
    · intro h1
      have h1_1 : st5.mem (ptr + OFF_MIN1_HAS) = 1 := by rw [h5_m1h]; rw [hfin_m1h] at h1; exact h1
      have h2_1 : st6.mem (ptr + OFF_MIN2_HAS) = 1 := by
        rw [h6_m2h, hhas_bool]; rw [hfin_m1h] at h1; exact h1
      obtain ⟨hk1, _⟩ := h5_m1nz h1_1
      obtain ⟨hk2, _⟩ := h6_m2nz h2_1
      have hm1v_ok : NumPtrOk st_hp.mem arenaHi hp2 h L (nodeField st_hp.mem nodesBase x OFF_MIN1_VAL) := by
        rw [hfin_m1v]; exact numPtrOk_congr le_rfl hag_fin_st5 hk1
      have hm2v_ok : NumPtrOk st_hp.mem arenaHi hp2 h L (nodeField st_hp.mem nodesBase x OFF_MIN2_VAL) := by
        rw [hfin_m2v]; exact numPtrOk_congr le_rfl hag_fin (by simpa using hk2)
      have hw0 : 0 < 2 ^ w := Nat.pow_pos (by decide)
      have hx_lt_pow : x < 2 ^ w := by
        have hst : 1 ≤ NODE_STRIDE := by decide
        have h1' : x ≤ NODE_STRIDE * x := Nat.le_mul_of_pos_left x hst
        have h2' : NODE_STRIDE * x < nodesBase + NODE_STRIDE * x + NODE_STRIDE :=
          lt_of_le_of_lt (Nat.le_add_left _ nodesBase) (Nat.lt_add_of_pos_right (by decide))
        exact lt_trans (lt_of_le_of_lt h1' h2') (lt_of_le_of_lt hx_arena (lt_of_le_of_lt harena hhp₀_lt))
      have hsid : ∀ s ∈ steps, s.nodeId < 2 ^ w := by
        intro s hs
        rw [hsteps_split] at hs
        simp only [List.mem_append] at hs
        rcases hs with (hs | hs) | hs
        · exact evalMemSteps_nodeId_lt hbase hpre.hl false 0 s hs
        · simp only [nodeOwnRawStep] at hs
          split_ifs at hs with hhe
          · simp at hs
          · rw [Option.map_some, Option.toList_some, List.mem_singleton] at hs
            subst hs
            simp only [RawStep.addDeltaMod]
            split_ifs; exact hx_lt_pow
          · rw [Option.map_some, Option.toList_some, List.mem_singleton] at hs
            subst hs
            simp only [RawStep.addDeltaMod]
            split_ifs; exact hx_lt_pow
        · exact evalMemSteps_nodeId_lt hbase hpre.hr false 0 s hs
      have h1_fl := listIntMinAgg_endpoints_lt hw0
        (xs := steps.map fun s => (s.nodeId, s.dirAvail)) (by
          intro q hq
          simp only [List.mem_map] at hq
          rcases hq with ⟨s, hs, rfl⟩
          exact hsid s hs)
      have h2_fl := listIntMinAgg_endpoints_lt hw0
        (xs := steps.map fun s => (s.nodeId, s.flip.dirAvail)) (by
          intro q hq
          simp only [List.mem_map] at hq
          rcases hq with ⟨s, hs, rfl⟩
          exact hsid s hs)
      change _ ∧ _ ∧ nodeField st_hp.mem nodesBase x OFF_MIN1_FIRST < 2 ^ w ∧
        nodeField st_hp.mem nodesBase x OFF_MIN1_LAST < 2 ^ w ∧
        nodeField st_hp.mem nodesBase x OFF_MIN2_FIRST < 2 ^ w ∧
        nodeField st_hp.mem nodesBase x OFF_MIN2_LAST < 2 ^ w
      rw [hfin_hp, hfin_m1f, hfin_m1l, hfin_m2f, hfin_m2l]
      exact ⟨hm1v_ok, hm2v_ok, h1_fl.1, h1_fl.2, h2_fl.1, h2_fl.2⟩
    · intro hz1
      have h1_0 : st5.mem (ptr + OFF_MIN1_HAS) = 0 := by rw [h5_m1h]; rw [hfin_m1h] at hz1; exact hz1
      have h2_0 : st6.mem (ptr + OFF_MIN2_HAS) = 0 := by
        rw [h6_m2h, hhas_bool]; rw [hfin_m1h] at hz1; exact hz1
      obtain ⟨hv1, hf1, hl1⟩ := h5_m1z h1_0
      obtain ⟨hv2, hf2, hl2⟩ := h6_m2z h2_0
      exact ⟨by rw [hfin_m1v]; exact hv1, by rw [hfin_m1f]; rw [h5_m1f] at hf1; exact hf1,
        by rw [hfin_m1l]; rw [h5_m1l] at hl1; exact hl1,
        by rw [hfin_m2v]; exact hv2, by rw [hfin_m2f]; rw [h6_m2f] at hf2; exact hf2,
        by rw [hfin_m2l]; rw [h6_m2l] at hl2; exact hl2⟩
    · have hrev_f0 : revFlag mem₀ nodesBase x = false := by simp [revFlag, hpre.hrev0]
      have hrev_f1 : revFlag st_hp.mem nodesBase x = false := by
        simp [revFlag, hfin_static OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hpre.hrev0]
      have hseq_eq : (AuxTree.node x l r).evalInorder (revFlag st_hp.mem nodesBase) false = seq := by
        simp only [AuxTree.evalInorder, hrev_f1, seq, seq_l, seq_r]
        rw [evalInorder_agree_of_list (fun u hu => hl_agree u hu OFF_REV (by decide)) false,
          evalInorder_agree_of_list (fun u hu => hr_agree u hu OFF_REV (by decide)) false]
      have hvc_fin : listVcnt st_hp.mem nodesBase seq = listVcnt mem₀ nodesBase seq := by
        apply listVcnt_agree_of_mem
        intro u hu
        simp only [seq, List.mem_append, List.mem_singleton] at hu
        rcases hu with (hl_u | rfl) | hr_u
        · have hu_l := (AuxTree.evalInorder_perm _ _ _).mem_iff.1 hl_u
          exact hl_agree u hu_l OFF_ISV (by decide)
        · exact hfin_static OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        · have hu_r := (AuxTree.evalInorder_perm _ _ _).mem_iff.1 hr_u
          exact hr_agree u hu_r OFF_ISV (by decide)
      refine ⟨by rw [hseq_eq, hvc_fin, hfin_vcnt], ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsteps_fin]; exact hfin_cf_val
      · rw [hsteps_fin]; exact hfin_cb_val
      · rw [hsteps_fin, hfin_m1h, ← hhas_iff1]; cases agg1_tgt.has <;> simp
      · rw [hsteps_fin]
        have hm1_val : optIntVal st_hp.mem h L (nodeField st_hp.mem nodesBase x OFF_MIN1_VAL) =
            if agg1_tgt.has then agg1_tgt.val else 0 := by
          by_cases hh : agg1_tgt.has = true
          · have h1_1 : st5.mem (ptr + OFF_MIN1_HAS) = 1 := by rw [h5_m1h, hh]; simp
            obtain ⟨hk1, hv1⟩ := h5_m1nz h1_1
            have hnz_v : st5.mem (ptr + OFF_MIN1_VAL) ≠ 0 := hk1.1
            have hinv : intVal st_hp.mem (st5.mem (ptr + OFF_MIN1_VAL)) h L = intVal st5.mem (st5.mem (ptr + OFF_MIN1_VAL)) h L :=
              intVal_agree_heap hag_fin_st5 hk1.2.1 hk1.2.2.1
            simp only [hh, ↓reduceIte, hfin_m1v, optIntVal, hnz_v, hinv, hv1]
          · have hf : agg1_tgt.has = false := Bool.eq_false_iff.mpr hh
            have h1_0 : st5.mem (ptr + OFF_MIN1_HAS) = 0 := by rw [h5_m1h, hf]; simp
            have hv0 := (h5_m1z h1_0).1
            simp only [hf, Bool.false_eq_true, ↓reduceIte, hfin_m1v, hv0, optIntVal]
        have hagg1_has_f : agg1_tgt.has = false → agg1_tgt = ⟨false, 0, 0, 0⟩ :=
          listIntMinAgg_false_eq
        by_cases hh : agg1_tgt.has = true
        · simp only [nodeIntMinAgg1, hfin_m1h, hfin_m1f, hfin_m1l, hm1_val, hh, ↓reduceIte,
            ne_eq, one_ne_zero, not_false_eq_true, decide_true]
          exact (show agg1_tgt = ⟨true, agg1_tgt.val, agg1_tgt.first, agg1_tgt.last⟩ by
            rcases h : agg1_tgt with ⟨ha, va, fa, la⟩
            rw [h] at hh
            exact congrArg (fun b => IntMinAgg.mk b va fa la) hh).symm
        · have hf := Bool.eq_false_iff.mpr hh
          have hh0 := hagg1_has_f hf
          have h1_0 : st5.mem (ptr + OFF_MIN1_HAS) = 0 := by rw [h5_m1h, hf]; simp
          obtain ⟨_, hf1_0, hl1_0⟩ := h5_m1z h1_0
          rw [h5_m1f] at hf1_0; rw [h5_m1l] at hl1_0
          simp only [nodeIntMinAgg1, hfin_m1h, hfin_m1f, hfin_m1l, hm1_val, hf, Bool.false_eq_true,
            ↓reduceIte, ne_eq, not_true_eq_false, decide_false, hf1_0, hl1_0]
          exact hh0.symm
      · rw [hsteps_fin]
        have hm2_val : optIntVal st_hp.mem h L (nodeField st_hp.mem nodesBase x OFF_MIN2_VAL) =
            if agg2_tgt.has then agg2_tgt.val else 0 := by
          by_cases hh : agg2_tgt.has = true
          · have h2_1 : st6.mem (ptr + OFF_MIN2_HAS) = 1 := by rw [h6_m2h, hh]; simp
            obtain ⟨hk2, hv2⟩ := h6_m2nz h2_1
            have hnz_v : st6.mem (ptr + OFF_MIN2_VAL) ≠ 0 := hk2.1
            have hinv : intVal st_hp.mem (st6.mem (ptr + OFF_MIN2_VAL)) h L = intVal st6.mem (st6.mem (ptr + OFF_MIN2_VAL)) h L :=
              intVal_agree_heap hag_fin hk2.2.1 hk2.2.2.1
            simp only [hh, ↓reduceIte, hfin_m2v, optIntVal, hnz_v, hinv, hv2]
          · have hf : agg2_tgt.has = false := Bool.eq_false_iff.mpr hh
            have h2_0 : st6.mem (ptr + OFF_MIN2_HAS) = 0 := by rw [h6_m2h, hf]; simp
            have hv0 := (h6_m2z h2_0).1
            simp only [hf, Bool.false_eq_true, ↓reduceIte, hfin_m2v, hv0, optIntVal]
        have hagg2_has_f : agg2_tgt.has = false → agg2_tgt = ⟨false, 0, 0, 0⟩ :=
          listIntMinAgg_false_eq
        by_cases hh : agg2_tgt.has = true
        · simp only [nodeIntMinAgg2, hfin_m2h, hfin_m2f, hfin_m2l, hm2_val, hh, ↓reduceIte,
            ne_eq, one_ne_zero, not_false_eq_true, decide_true]
          exact (show agg2_tgt = ⟨true, agg2_tgt.val, agg2_tgt.first, agg2_tgt.last⟩ by
            rcases h : agg2_tgt with ⟨ha, va, fa, la⟩
            rw [h] at hh
            exact congrArg (fun b => IntMinAgg.mk b va fa la) hh).symm
        · have hf := Bool.eq_false_iff.mpr hh
          have hh0 := hagg2_has_f hf
          have h2_0 : st6.mem (ptr + OFF_MIN2_HAS) = 0 := by rw [h6_m2h, hf]; simp
          obtain ⟨_, hf2_0, hl2_0⟩ := h6_m2z h2_0
          rw [h6_m2f] at hf2_0; rw [h6_m2l] at hl2_0
          simp only [nodeIntMinAgg2, hfin_m2h, hfin_m2f, hfin_m2l, hm2_val, hf, Bool.false_eq_true,
            ↓reduceIte, ne_eq, not_true_eq_false, decide_false, hf2_0, hl2_0]
          exact hh0.symm
  have hcb : (1 + (32 + (33 + (c_fwd + (c_bwd + (c_m1 + (c_m2 + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
      (st_hp.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ K_PULL L := by
    rw [hfin_hp, sub_split_le hle1 hle2]
    exact pull_total_cost_le hc_fwd hc_bwd hc_m1 hc_m2
  refine ⟨st_hp, _, hfull, hcb, by rw [hfin_hp]; exact le_trans hle1 hle2,
    by rw [hfin_hp]; exact le_trans hhi2 (by rw [← h4L2, ← Nat.add_assoc]; exact Nat.add_le_add_right hhi1 (2 * L)),
    htree, hfin_out, hfin_static,
    ⟨by have : nodesBase - 1 < nodesBase := Nat.sub_lt (le_trans (by decide) hnb) (by decide)
        exact lt_of_lt_of_le this (Nat.le_add_right _ _),
      harena, by rw [hfin_hp]; exact le_trans hle1 hle2,
      hz, by rw [hfin_hp]; exact hfin_hz, fun i hi => ?_⟩⟩
  rcases hi with ⟨hi_lo, hi_ne⟩ | ⟨hi_ar, hi_hp⟩
  · have hlt_ptr : i < ptr := lt_of_lt_of_le hi_lo
      (Nat.add_le_add_left (Nat.le_mul_of_pos_right NODE_STRIDE hx1) nodesBase)
    have hlt_hp : i < hp₀ :=
      lt_of_lt_of_le (lt_trans hlt_ptr (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hx_arena)) harena
    exact hfin_out i hi_ne (Or.inl hlt_ptr) hlt_hp
  · exact hag_hp0 i hi_ar hi_hp

end

end MinCostFlow.LinkCut.Prog
