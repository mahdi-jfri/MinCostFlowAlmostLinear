module

public import MinCostFlow.LinkCut.Prog.MathForestExposeInvs

/-!
# Expose Phase 1 (`exposePhase1DetachStmt`) and Shared Framing Helpers

Proves `exposePhase1_runs`, plus shared helper lemmas `splay_lct_tree_headroom_lt`,
`pull_lct_runs`, `lctFrame_three_slot_updates`, and `lctVSize_ge_treeSize_of_ppar`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PullAndPhase1Helpers

theorem splay_lct_tree_headroom_lt {w h L : ℕ} {mem : ℕ → ℕ} {b n cap : ℕ}
    {trees : List AuxTree} {t : AuxTree} {x : ℕ}
    (hsf : SplayForestOk w h L mem (lctNodesBase b) cap trees)
    (hcap_eq : cap = lctCap n) (ht : t ∈ trees) (hx : x ∈ t.toList)
    (hhp_room : mem (lctNodesBase b - 1) + 6000 * (L + 1) * (n + 2) < 2 ^ w) :
    mem (lctNodesBase b - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x < 2 ^ w := by
  have hd_lt : t.depthOf x < lctCap n := by
    rw [← hcap_eq]
    exact lt_of_lt_of_le (auxTree_depthOf_lt_length hx) (splayForestOk_toList_length_le hsf ht)
  have hs := splay_headroom_le L n (t.depthOf x) hd_lt
  omega

theorem pull_lct_runs {w h L nodesBase cap parId pp x hp0 pos : ℕ}
    (p : Program) (sp : SplayProcs) (mem_safe mem₀ : ℕ → ℕ)
    (hp_has : p.HasAt sp.numZero (splayBodies sp h))
    (hp_base : ∃ spB, sp = SplayProcs.atBase spB)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena_safe : nodesBase + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hz0_safe : SlotZeroOk mem_safe nodesBase)
    (hsafe : SafeMem mem_safe nodesBase cap hp0 mem₀)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + 4 * L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {l r : AuxTree} (hx_le : x ≤ cap) (hx_nin_l : x ∉ l.toList) (hx_nin_r : x ∉ r.toList)
    (hpre : PullPre w h L mem₀ nodesBase cap x l r parId pp) :
    ∀ ω, ∃ st' c,
      Runs w p ω (pullBody sp) (startState [nodesBase, x] mem₀ pos) (.returned 0) st' c ∧
      SafeMem mem_safe nodesBase cap hp0 st'.mem ∧
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
  rcases hp_base with ⟨spB, rfl⟩
  rcases pullBody_runs p (SplayProcs.atBase spB) mem₀ pos hp_ok hbase hnb hL_hdr harena hz hhp_lt h0
      hx_nin_l hx_nin_r hpre ω with
    ⟨st', c, hr, hc, hle, hhi, htm, hout, hnonAgg, hfr⟩
  rcases hr with ⟨fuel, hex⟩
  have hsafe' : SafeMem mem_safe nodesBase cap hp0 st'.mem :=
    (pull_safeExec hp_has hnb harena_safe hz0_safe hx_le (by simp [startState]) (by simp [startState])
      hsafe hex).2
  exact ⟨st', c, ⟨fuel, hex⟩, hsafe', hc, hle, hhi, htm, hout, hnonAgg, hfr⟩

theorem lctFrame_three_slot_updates {nb cap y1 off1 v1 y2 off2 v2 y3 off3 v3 : ℕ}
    {mem : ℕ → ℕ}
    (hy1a : 1 ≤ y1) (hy1b : y1 ≤ cap) (hoff1 : off1 < NODE_STRIDE)
    (hy2a : 1 ≤ y2) (hy2b : y2 ≤ cap) (hoff2 : off2 < NODE_STRIDE)
    (hy3a : 1 ≤ y3) (hy3b : y3 ≤ cap) (hoff3 : off3 < NODE_STRIDE)
    (harena : nb + NODE_STRIDE * (cap + 1) ≤ mem (nb - 1))
    (hz : ZeroFrom mem (mem (nb - 1))) (hnb : 3 ≤ nb) :
    let m1 := Function.update mem (nb + NODE_STRIDE * y1 + off1) v1
    let m2 := Function.update m1 (nb + NODE_STRIDE * y2 + off2) v2
    let m3 := Function.update m2 (nb + NODE_STRIDE * y3 + off3) v3
    LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem m3 := by
  intro m1 m2 m3
  have hbound : ∀ y off, 1 ≤ y → y ≤ cap → off < NODE_STRIDE →
      nb + NODE_STRIDE ≤ nb + NODE_STRIDE * y + off ∧
      nb + NODE_STRIDE * y + off < nb + NODE_STRIDE * (cap + 1) := by
    intro y off hy1 hy2 hoff
    have hmul1 : NODE_STRIDE ≤ NODE_STRIDE * y := Nat.le_mul_of_pos_right NODE_STRIDE hy1
    have hmul2 : NODE_STRIDE * y + NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left NODE_STRIDE (Nat.succ_le_succ hy2)
    omega
  have hb1 := hbound y1 off1 hy1a hy1b hoff1
  have hb2 := hbound y2 off2 hy2a hy2b hoff2
  have hb3 := hbound y3 off3 hy3a hy3b hoff3
  have hhdr : nb - 1 < nb + NODE_STRIDE := by unfold NODE_STRIDE; omega
  have hf1 : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem m1 :=
    lctFrame_update_arena hb1.1 hb1.2 hhdr harena hz
  have hf2 : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) m1 m2 :=
    lctFrame_update_arena hb2.1 hb2.2 hhdr (le_trans hf1.2.1 hf1.2.2.1) hf1.2.2.2.2.1
  have hf3 : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) m2 m3 :=
    lctFrame_update_arena hb3.1 hb3.2 hhdr (le_trans hf2.2.1 hf2.2.2.1) hf2.2.2.2.2.1
  exact lctFrame_trans hf1 (lctFrame_trans hf2 hf3)

theorem slot_addr_inj {nb y₁ o₁ y₂ o₂ : ℕ} (h1 : o₁ < NODE_STRIDE) (h2 : o₂ < NODE_STRIDE)
    (heq : nb + NODE_STRIDE * y₁ + o₁ = nb + NODE_STRIDE * y₂ + o₂) : y₁ = y₂ ∧ o₁ = o₂ := by
  unfold NODE_STRIDE at h1 h2 heq; omega

theorem slot_disjoint_of_ne {nb u x off : ℕ} (hne : u ≠ x) (hoff : off < NODE_STRIDE) :
    nb + NODE_STRIDE * u + off < nb + NODE_STRIDE * x ∨
    nb + NODE_STRIDE * x + NODE_STRIDE ≤ nb + NODE_STRIDE * u + off := by
  rcases lt_or_gt_of_ne hne with h | h
  · left
    have hmul : NODE_STRIDE * (u + 1) ≤ NODE_STRIDE * x := Nat.mul_le_mul_left NODE_STRIDE h
    rw [Nat.mul_succ] at hmul; omega
  · right
    have hmul : NODE_STRIDE * (x + 1) ≤ NODE_STRIDE * u := Nat.mul_le_mul_left NODE_STRIDE h
    rw [Nat.mul_succ] at hmul; omega

theorem slot_lt_of_arena {nb cap hp u off : ℕ} (hu : u ≤ cap) (hoff : off < NODE_STRIDE)
    (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp) :
    nb + NODE_STRIDE * u + off < hp := by
  have hmul : NODE_STRIDE * u ≤ NODE_STRIDE * cap := Nat.mul_le_mul_left NODE_STRIDE hu
  rw [Nat.mul_succ] at harena; omega

theorem lctVSize_ge_treeSize_of_ppar {w h L P b n : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {trees : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees mem)
    {t : AuxTree} (ht : t ∈ trees) {p : ℕ}
    (hpp : nodeField mem (lctNodesBase b) t.rootId OFF_PPAR = p) :
    t.treeSize (lctVSize mem (lctNodesBase b) (lctCap n)) ≤
      lctVSize mem (lctNodesBase b) (lctCap n) p := by
  have hne : ∀ s ∈ trees, lctTreeSeq mem (lctNodesBase b) (lctCap n) s.rootId ≠ [] := fun s hs => by
    rw [hi.sf.lctTreeSeq_eq hs]
    exact auxTree_eval_ne_nil_of_ne_leaf (hi.sf.trees_ok s hs).1
  have hpp_le : ∀ s ∈ trees, nodeField mem (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n := fun s hs =>
    hi.ppar_le_cap s hs
  have hsz_eq := treeSize_lctVSize_eq_repSize hi.sf hi.subdivOk.1 hpp_le hne ht
  have hdcs : dashedChildSize mem (lctNodesBase b) (lctCap n) t.rootId =
      t.treeSize (lctVSize mem (lctNodesBase b) (lctCap n)) := by
    simp only [dashedChildSize]
    cases hts : lctTreeSeq mem (lctNodesBase b) (lctCap n) t.rootId with
    | nil => exact absurd hts (hne t ht)
    | cons hd _ => simpa [hts] using hsz_eq.symm
  have hrt_in : t.rootId ∈ auxRootIds mem (lctNodesBase b) (lctCap n) :=
    hi.sf.auxRootIds_perm.mem_iff.2 (List.mem_map.2 ⟨t, ht, rfl⟩)
  have hfilt : t.rootId ∈ (auxRootIds mem (lctNodesBase b) (lctCap n)).filter
      (fun r => decide (nodeField mem (lctNodesBase b) r OFF_PPAR = p)) :=
    List.mem_filter.2 ⟨hrt_in, by simp [hpp]⟩
  have hmem_map : dashedChildSize mem (lctNodesBase b) (lctCap n) t.rootId ∈
      ((auxRootIds mem (lctNodesBase b) (lctCap n)).filter
        (fun r => decide (nodeField mem (lctNodesBase b) r OFF_PPAR = p))).map
        (dashedChildSize mem (lctNodesBase b) (lctCap n)) :=
    List.mem_map.2 ⟨t.rootId, hfilt, rfl⟩
  rw [← hdcs]
  exact List.le_sum_of_mem hmem_map

end PullAndPhase1Helpers

section Phase1Execution

theorem exposePhase1_runs {w h L P b n v hp0 pos : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {l r : AuxTree} {rest : List AuxTree}
    (p : Program) (sp : SplayProcs) (mem_safe mem₀ : ℕ → ℕ) (r₀ : ℕ → ℕ)
    (hp_has : p.HasAt sp.numZero (splayBodies sp h))
    (hp_base : ∃ spB, sp = SplayProcs.atBase spB)
    (hp_ok : SplayProgramOk w h p sp)
    (hz0_safe : SlotZeroOk mem_safe (lctNodesBase b))
    (harena_safe : lctArenaHi b (lctCap n) ≤ hp0)
    (hsafe₀ : SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 mem₀)
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (.node (v + 1) l r :: rest) mem₀)
    (hv : v < n)
    (hrev0 : nodeField mem₀ (lctNodesBase b) (v + 1) OFF_REV = 0)
    (hht0 : nodeField mem₀ (lctNodesBase b) (v + 1) OFF_HAS_TAG = 0)
    (hz₀ : ZeroFrom mem₀ (mem₀ (lctNodesBase b - 1)))
    (hhp_room : mem₀ (lctNodesBase b - 1) + K_PULL L + 4 * L < 2 ^ w)
    (hr0_0 : r₀ 0 = lctNodesBase b) (hr0_1 : r₀ 1 = v + 1) :
    ∀ ω, ∃ st₁ c₁,
      Runs w p ω (exposePhase1DetachStmt sp) { mem := mem₀, regs := r₀, pos := pos } .normal st₁ c₁ ∧
      LctExposeInvs w h L P b n freeEdges edgeMap
        (if r = .leaf then .node (v + 1) l .leaf :: rest else .node (v + 1) l .leaf :: r :: rest) st₁.mem ∧
      SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 st₁.mem ∧
      LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1))
        (lctNodesBase b - 1) mem₀ st₁.mem ∧
      (∀ u, lctAuxParent st₁.mem (lctNodesBase b) (lctCap n) u =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap n) u) ∧
      (∀ z, lctRepSize st₁.mem (lctNodesBase b) (lctCap n) z =
        lctRepSize mem₀ (lctNodesBase b) (lctCap n) z) ∧
      st₁.regs 0 = lctNodesBase b ∧ st₁.regs 1 = v + 1 ∧ st₁.regs 5 = v + 1 ∧
      st₁.regs 6 = nodeField st₁.mem (lctNodesBase b) (v + 1) OFF_PPAR ∧
      nodeField st₁.mem (lctNodesBase b) (v + 1) OFF_PPAR =
        nodeField mem₀ (lctNodesBase b) (v + 1) OFF_PPAR ∧
      ((AuxTree.node (v + 1) l .leaf).evalInorder (revFlag st₁.mem (lctNodesBase b)) false).getLast? =
        some (v + 1) ∧
      (AuxTree.node (v + 1) l .leaf).treeSize (lctVSize st₁.mem (lctNodesBase b) (lctCap n)) =
        (AuxTree.node (v + 1) l r).treeSize (lctVSize mem₀ (lctNodesBase b) (lctCap n)) ∧
      c₁ + (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st₁.mem b n ≤
        lctPhi L mem₀ b n + K_PULL L + C_HEAVY L + 80 := by
  intro ω
  set x := v + 1
  set nb := lctNodesBase b
  set cap := lctCap n
  let trees₁ := if r = .leaf then .node x l .leaf :: rest else .node x l .leaf :: r :: rest
  have hnb3 : 3 ≤ nb := hi.sf.2.2.1
  have harena₀ : nb + NODE_STRIDE * (cap + 1) ≤ mem₀ (nb - 1) := hi.sf.2.2.2.1
  have hL₀ : mem₀ (nb - 3) = L := hi.sf.2.2.2.2.1
  have hhp₀ : mem₀ (nb - 1) < 2 ^ w := hi.sf.2.2.2.2.2.1
  have hbase_w : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := lt_of_le_of_lt harena₀ hhp₀
  have hstride_w : NODE_STRIDE < 2 ^ w := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  have hx_tok := hi.sf.trees_ok (.node x l r) (by simp [x])
  have hx_b : 1 ≤ x ∧ x ≤ cap := hx_tok.2.2.nodup_perm_mem (y := x) (by simp [AuxTree.toList])
  have hptr_lt : nb + NODE_STRIDE * x < 2 ^ w := by
    simpa using nodeAddr_lt_pow hbase_w hx_b.2 (by decide : 0 < NODE_STRIDE)
  have hright_lt : nb + NODE_STRIDE * x + OFF_RIGHT < 2 ^ w :=
    nodeAddr_lt_pow hbase_w hx_b.2 (by decide : OFF_RIGHT < NODE_STRIDE)
  have hpp_lt : nb + NODE_STRIDE * x + OFF_PPAR < 2 ^ w :=
    nodeAddr_lt_pow hbase_w hx_b.2 (by decide : OFF_PPAR < NODE_STRIDE)
  have hnd_x : (AuxTree.node x l r).toList.Nodup :=
    list_nodup_of_flatMap_nodup
      (hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
      (by simp [x])
  have hr2 : Runs w p ω (Stmt.assign 2 (nodePtrExpr 0 1))
      { mem := mem₀, regs := r₀, pos := pos } .normal
      { mem := mem₀, regs := Function.update r₀ 2 (nb + NODE_STRIDE * x), pos := pos } _ :=
    runs_assign_iff.mpr ⟨nb + NODE_STRIDE * x,
      eval_nodePtrExpr hstride_w hr0_0 hr0_1 hptr_lt, rfl, rfl, rfl⟩
  let r₂ := Function.update r₀ 2 (nb + NODE_STRIDE * x)
  have hr₂_0 : r₂ 0 = nb := by simp [r₂, hr0_0]
  have hr₂_1 : r₂ 1 = x := by simp [r₂, hr0_1]
  have hr₂_2 : r₂ 2 = nb + NODE_STRIDE * x := by simp [r₂]
  have hr3 : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_RIGHT))
      { mem := mem₀, regs := r₂, pos := pos } .normal
      { mem := mem₀, regs := Function.update r₂ 3 (nodeField mem₀ nb x OFF_RIGHT), pos := pos } _ :=
    runs_assign_iff.mpr ⟨nodeField mem₀ nb x OFF_RIGHT,
      eval_fieldLoadExpr hr₂_2 hright_lt, rfl, rfl, rfl⟩
  let r₃ := Function.update r₂ 3 (nodeField mem₀ nb x OFF_RIGHT)
  have hr₃_0 : r₃ 0 = nb := by simp [r₃, hr₂_0]
  have hr₃_1 : r₃ 1 = x := by simp [r₃, hr₂_1]
  have hr₃_2 : r₃ 2 = nb + NODE_STRIDE * x := by simp [r₃, hr₂_2]
  have hr₃_3 : r₃ 3 = nodeField mem₀ nb x OFF_RIGHT := by simp [r₃]
  cases hr_eq : r with
  | leaf =>
      have hright0 : nodeField mem₀ nb x OFF_RIGHT = 0 := by
        have htm := hx_tok.2.2; rw [hr_eq] at htm; exact htm.2.2.2.1
      have hcond : Runs w p ω (Stmt.cond (.reg 3)
          (Stmt.assign 4 (nodePtrExpr 0 3) ;;
           Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.const 0) ;;
           Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.reg 1) ;;
           Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.const 0) ;;
           Stmt.call 10 sp.pull [.reg 0, .reg 1]) Stmt.nop)
          { mem := mem₀, regs := r₃, pos := pos } .normal
          { mem := mem₀, regs := r₃, pos := pos } ((Expr.reg 3).size + 1 + 1) := by
        refine runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, hr₃_3, hright0], ?_, rfl⟩
        simp [runs_nop_iff]
      have ha5 : Runs w p ω (Stmt.assign 5 (.reg 1))
          { mem := mem₀, regs := r₃, pos := pos } .normal
          { mem := mem₀, regs := Function.update r₃ 5 x, pos := pos } _ :=
        runs_assign_iff.mpr ⟨x, by simp [Expr.eval, hr₃_1], rfl, rfl, rfl⟩
      let r₅ := Function.update r₃ 5 x
      have hr₅_2 : r₅ 2 = nb + NODE_STRIDE * x := by simp [r₅, hr₃_2]
      have ha6 : Runs w p ω (Stmt.assign 6 (fieldLoadExpr 2 OFF_PPAR))
          { mem := mem₀, regs := r₅, pos := pos } .normal
          { mem := mem₀, regs := Function.update r₅ 6 (nodeField mem₀ nb x OFF_PPAR), pos := pos } _ :=
        runs_assign_iff.mpr ⟨nodeField mem₀ nb x OFF_PPAR,
          eval_fieldLoadExpr hr₅_2 hpp_lt, rfl, rfl, rfl⟩
      have hseq := runs_seq_normal hr2 (runs_seq_normal hr3 (runs_seq_normal hcond (runs_seq_normal ha5 ha6)))
      have hrev_x0 : revFlag mem₀ nb x = false := by simp [revFlag, nb, x, hrev0]
      have hlast_eq : ((AuxTree.node x l .leaf).evalInorder (revFlag mem₀ nb) false).getLast? = some x := by
        simp [AuxTree.evalInorder, hrev_x0]
      refine ⟨_, _, hseq, by simpa [trees₁, hr_eq, x] using hi, hsafe₀,
        lctFrame_refl (by unfold NODE_STRIDE; omega) harena₀ hz₀,
        fun _ => rfl, fun _ => rfl,
        by simp [r₅, hr₃_0], by simp [r₅, hr₃_1], by simp [r₅], by simp, rfl,
        hlast_eq, by simp, ?_⟩
      simp only [Nat.sub_self, Nat.add_zero, Expr.size, fieldLoadExpr, fieldAddrExpr, nodePtrExpr]
      omega
  | node rc rl rr =>
      have hrc_eq : nodeField mem₀ nb x OFF_RIGHT = rc := by
        have htm := hx_tok.2.2; rw [hr_eq] at htm; exact htm.2.2.2.1
      have hrc_b : 1 ≤ rc ∧ rc ≤ cap :=
        hx_tok.2.2.nodup_perm_mem (y := rc) (by simp [hr_eq, AuxTree.toList])
      have hx_ne_rc : x ≠ rc := by
        have hnr := auxTree_nodup_id_nin_right (by simpa [hr_eq] using hnd_x)
        intro heq; apply hnr; rw [heq]; simp [AuxTree.toList]
      have hrc_ptr_lt : nb + NODE_STRIDE * rc < 2 ^ w := by
        simpa using nodeAddr_lt_pow hbase_w hrc_b.2 (by decide : 0 < NODE_STRIDE)
      have hrc_par_lt : nb + NODE_STRIDE * rc + OFF_PARENT < 2 ^ w :=
        nodeAddr_lt_pow hbase_w hrc_b.2 (by decide : OFF_PARENT < NODE_STRIDE)
      have hrc_pp_lt : nb + NODE_STRIDE * rc + OFF_PPAR < 2 ^ w :=
        nodeAddr_lt_pow hbase_w hrc_b.2 (by decide : OFF_PPAR < NODE_STRIDE)
      have hrc_ne0 : rc ≠ 0 := by omega
      have hcond_a4 : Runs w p ω (Stmt.assign 4 (nodePtrExpr 0 3))
          { mem := mem₀, regs := r₃, pos := pos } .normal
          { mem := mem₀, regs := Function.update r₃ 4 (nb + NODE_STRIDE * rc), pos := pos } _ :=
        runs_assign_iff.mpr ⟨nb + NODE_STRIDE * rc,
          eval_nodePtrExpr hstride_w hr₃_0 (by dsimp only; rw [hr₃_3, hrc_eq]) hrc_ptr_lt, rfl, rfl, rfl⟩
      let r₄ := Function.update r₃ 4 (nb + NODE_STRIDE * rc)
      have hr₄_0 : r₄ 0 = nb := by simp [r₄, hr₃_0]
      have hr₄_1 : r₄ 1 = x := by simp [r₄, hr₃_1]
      have hr₄_2 : r₄ 2 = nb + NODE_STRIDE * x := by simp [r₄, hr₃_2]
      have hr₄_4 : r₄ 4 = nb + NODE_STRIDE * rc := by simp [r₄]
      have hw0 : (0 : ℕ) < 2 ^ w := Nat.zero_lt_of_lt hhp₀
      have hs1 : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.const 0))
          { mem := mem₀, regs := r₄, pos := pos } .normal
          { mem := Function.update mem₀ (nb + NODE_STRIDE * rc + OFF_PARENT) 0, regs := r₄, pos := pos } _ :=
        runs_store_iff.mpr ⟨nb + NODE_STRIDE * rc + OFF_PARENT, 0,
          eval_fieldAddrExpr hr₄_4 hrc_par_lt, Expr.eval_const hw0, rfl, rfl, rfl⟩
      let m₁ := Function.update mem₀ (nb + NODE_STRIDE * rc + OFF_PARENT) 0
      have hs2 : Runs w p ω (Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.reg 1))
          { mem := m₁, regs := r₄, pos := pos } .normal
          { mem := Function.update m₁ (nb + NODE_STRIDE * rc + OFF_PPAR) x, regs := r₄, pos := pos } _ :=
        runs_store_iff.mpr ⟨nb + NODE_STRIDE * rc + OFF_PPAR, x,
          eval_fieldAddrExpr hr₄_4 hrc_pp_lt, Expr.eval_reg_of_eq hr₄_1, rfl, rfl, rfl⟩
      let m₂ := Function.update m₁ (nb + NODE_STRIDE * rc + OFF_PPAR) x
      have hs3 : Runs w p ω (Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.const 0))
          { mem := m₂, regs := r₄, pos := pos } .normal
          { mem := Function.update m₂ (nb + NODE_STRIDE * x + OFF_RIGHT) 0, regs := r₄, pos := pos } _ :=
        runs_store_iff.mpr ⟨nb + NODE_STRIDE * x + OFF_RIGHT, 0,
          eval_fieldAddrExpr hr₄_2 hright_lt, Expr.eval_const hw0, rfl, rfl, rfl⟩
      let mem_ptr := Function.update m₂ (nb + NODE_STRIDE * x + OFF_RIGHT) 0
      have hnb1_ne_slot : ∀ y off, 1 ≤ y → off < NODE_STRIDE → nb - 1 ≠ nb + NODE_STRIDE * y + off := by
        intro y off hy1 _; unfold NODE_STRIDE; omega
      have hhp_ptr : mem_ptr (nb - 1) = mem₀ (nb - 1) := by
        dsimp only [mem_ptr, m₂, m₁]
        rw [Function.update_of_ne (hnb1_ne_slot x OFF_RIGHT hx_b.1 (by decide)),
          Function.update_of_ne (hnb1_ne_slot rc OFF_PPAR hrc_b.1 (by decide)),
          Function.update_of_ne (hnb1_ne_slot rc OFF_PARENT hrc_b.1 (by decide))]
      have hfr_0_ptr : LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem₀ mem_ptr :=
        lctFrame_three_slot_updates hrc_b.1 hrc_b.2 (by decide) hrc_b.1 hrc_b.2 (by decide)
          hx_b.1 hx_b.2 (by decide) harena₀ hz₀ hnb3
      have hz_ptr : ZeroFrom mem_ptr (mem_ptr (nb - 1)) := hfr_0_ptr.2.2.2.2.1
      have hsafe_ptr : SafeMem mem_safe nb cap hp0 mem_ptr :=
        SafeMem.update_struct hx_b.1 hx_b.2 (Nat.zero_le _) (Or.inr (Or.inl rfl))
          (SafeMem.update_struct hrc_b.1 hrc_b.2 hx_b.2 (Or.inr (Or.inr (Or.inr rfl)))
            (SafeMem.update_struct hrc_b.1 hrc_b.2 (Nat.zero_le _) (Or.inr (Or.inr (Or.inl rfl))) hsafe₀))
      have h0_ptr : SlotZeroOk mem_ptr nb := fun off hoff => by
        dsimp only [mem_ptr, m₂, m₁]
        have hne1 : nb + off ≠ nb + NODE_STRIDE * x + OFF_RIGHT := fun h => by
          have := (slot_addr_inj (y₁ := 0) (o₁ := off) (o₂ := OFF_RIGHT) hoff (by decide) (by simpa using h)).1
          omega
        have hne2 : nb + off ≠ nb + NODE_STRIDE * rc + OFF_PPAR := fun h => by
          have := (slot_addr_inj (y₁ := 0) (o₁ := off) (o₂ := OFF_PPAR) hoff (by decide) (by simpa using h)).1
          omega
        have hne3 : nb + off ≠ nb + NODE_STRIDE * rc + OFF_PARENT := fun h => by
          have := (slot_addr_inj (y₁ := 0) (o₁ := off) (o₂ := OFF_PARENT) hoff (by decide) (by simpa using h)).1
          omega
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_of_ne hne3]
        exact hi.sf.2.2.2.2.2.2.2.1 off hoff
      have hL_ptr : mem_ptr (nb - 3) = L := by
        dsimp only [mem_ptr, m₂, m₁]
        rw [Function.update_of_ne (by unfold NODE_STRIDE; omega),
          Function.update_of_ne (by unfold NODE_STRIDE; omega),
          Function.update_of_ne (by unfold NODE_STRIDE; omega)]
        exact hL₀
      have hptr_field : ∀ y off, off < NODE_STRIDE →
          (¬(y = x ∧ off = OFF_RIGHT) ∧ ¬(y = rc ∧ off = OFF_PPAR) ∧ ¬(y = rc ∧ off = OFF_PARENT)) →
          nodeField mem_ptr nb y off = nodeField mem₀ nb y off := by
        intro y off hoff ⟨hn1, hn2, hn3⟩
        dsimp only [nodeField, mem_ptr, m₂, m₁]
        have he1 : nb + NODE_STRIDE * y + off ≠ nb + NODE_STRIDE * x + OFF_RIGHT := fun h =>
          hn1 (slot_addr_inj hoff (by decide) h)
        have he2 : nb + NODE_STRIDE * y + off ≠ nb + NODE_STRIDE * rc + OFF_PPAR := fun h =>
          hn2 (slot_addr_inj hoff (by decide) h)
        have he3 : nb + NODE_STRIDE * y + off ≠ nb + NODE_STRIDE * rc + OFF_PARENT := fun h =>
          hn3 (slot_addr_inj hoff (by decide) h)
        rw [Function.update_of_ne he1, Function.update_of_ne he2, Function.update_of_ne he3]
      have hx_nin_l : x ∉ l.toList := auxTree_nodup_id_nin_left hnd_x
      have hx_left_eq : nodeField mem_ptr nb x OFF_LEFT = l.rootId := by
        rw [hptr_field x OFF_LEFT (by decide) ⟨fun h => by exact absurd h.2 (by decide), fun h => by exact absurd h.2 (by decide), fun h => by exact absurd h.2 (by decide)⟩]
        exact hx_tok.2.2.2.2.1
      have hx_right_eq : nodeField mem_ptr nb x OFF_RIGHT = 0 := by
        dsimp only [nodeField, mem_ptr]; exact Function.update_self _ _ _
      have hx_par_eq : nodeField mem_ptr nb x OFF_PARENT = 0 := by
        rw [hptr_field x OFF_PARENT (by decide) ⟨fun h => by exact absurd h.2 (by decide), fun h => hx_ne_rc h.1, fun h => hx_ne_rc h.1⟩]
        exact hx_tok.2.2.2.2.2.2.1
      have hx_pp_eq : nodeField mem_ptr nb x OFF_PPAR = nodeField mem₀ nb x OFF_PPAR := by
        rw [hptr_field x OFF_PPAR (by decide) ⟨fun h => by exact absurd h.2 (by decide), fun h => hx_ne_rc h.1, fun h => hx_ne_rc h.1⟩]
      have hrc_par_ptr : nodeField mem_ptr nb rc OFF_PARENT = 0 := by
        dsimp only [nodeField, mem_ptr, m₂, m₁]
        have h1 : nb + NODE_STRIDE * rc + OFF_PARENT ≠ nb + NODE_STRIDE * x + OFF_RIGHT := fun h =>
          hx_ne_rc (slot_addr_inj (by decide) (by decide) h).1.symm
        have h2 : nb + NODE_STRIDE * rc + OFF_PARENT ≠ nb + NODE_STRIDE * rc + OFF_PPAR := by
          unfold OFF_PARENT OFF_PPAR; omega
        rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_self]
      have hrc_pp_ptr : nodeField mem_ptr nb rc OFF_PPAR = x := by
        dsimp only [nodeField, mem_ptr, m₂]
        have h1 : nb + NODE_STRIDE * rc + OFF_PPAR ≠ nb + NODE_STRIDE * x + OFF_RIGHT := fun h =>
          hx_ne_rc (slot_addr_inj (by decide) (by decide) h).1.symm
        rw [Function.update_of_ne h1, Function.update_self]
      have hl_fields_ptr : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          nodeField mem_ptr nb u off = nodeField mem₀ nb u off := by
        intro u hu off hoff
        have hux : u ≠ x := fun h => hx_nin_l (h ▸ hu)
        have hurc : u ≠ rc := fun h => by
          have hnd' := hnd_x; rw [AuxTree.toList, List.nodup_append] at hnd'
          exact hnd'.2.2 u (by simp [hu]) rc (by simp [hr_eq, AuxTree.toList]) h
        exact hptr_field u off hoff ⟨fun he => hux he.1, fun he => hurc he.1, fun he => hurc he.1⟩
      have hheap_ptr : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nb - 1) → mem_ptr a = mem₀ a :=
        fun a ha ha' => hfr_0_ptr.2.2.2.2.2 a (Or.inr ⟨ha, ha'⟩)
      have hx_tok_tm : TreeMemMatch w h L mem₀ nb cap (.node x l (.node rc rl rr)) 0
          (nodeField mem₀ nb x OFF_PPAR) := by
        dsimp only [nb, cap]
        simpa [hr_eq, AuxTree.rootId] using hx_tok.2.2
      have hpre_p := pullPre_detach hbase_w hx_tok_tm (by simpa [hr_eq] using hnd_x)
        hrev0 hht0 hhp_ptr hx_left_eq hx_right_eq hx_par_eq hx_pp_eq
        (fun off hoff hne => hptr_field x off hoff ⟨fun h => hne h.2, fun h => hx_ne_rc h.1, fun h => hx_ne_rc h.1⟩)
        hl_fields_ptr hheap_ptr
      have hrp := pull_lct_runs (pos := pos) p sp mem_safe mem_ptr hp_has hp_base hp_ok hbase_w hnb3 hL_ptr
        harena_safe hz0_safe hsafe_ptr (by rw [hhp_ptr]; exact harena₀) hz_ptr
        (by rw [hhp_ptr]; dsimp only [nb] at *; omega) h0_ptr hx_b.2 hx_nin_l (by simp [AuxTree.toList]) hpre_p ω
      rcases hrp with ⟨st_p, c_p, hrun_p, hsafe_p, hc_p, hle_p, hhi_p, htm_p, hout_p, hnonAgg_p, hfr_p⟩
      have hcall_p : Runs w p ω (Stmt.call 10 sp.pull [.reg 0, .reg 1])
          { mem := mem_ptr, regs := r₄, pos := pos } .normal
          { mem := st_p.mem, regs := Function.update r₄ 10 0, pos := st_p.pos } (2 + c_p + 1) := by
        refine runs_call_iff.mpr ⟨[nb, x], pullBody sp, .returned 0, st_p, c_p, ?_, hp_ok.pull_eq, ?_, rfl, ?_, rfl⟩
        · simp [evalArgs, Expr.eval, hr₄_0, hr₄_1]
        · simpa [startState, hr₄_0, hr₄_1] using hrun_p
        · cases st_p; rfl
      have hthen := runs_seq_normal hcond_a4 (runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3 hcall_p)))
      have hcond_then := (runs_cond_iff (e := .reg 3)
          (st := { mem := mem₀, regs := r₃, pos := pos }) (t := Stmt.nop)).mpr
        ⟨rc, _, by simp [Expr.eval, hr₃_3, hrc_eq], by simpa [hrc_ne0] using hthen, rfl⟩
      let r₅₀ := Function.update r₄ 10 0
      have ha5 : Runs w p ω (Stmt.assign 5 (.reg 1))
          { mem := st_p.mem, regs := r₅₀, pos := st_p.pos } .normal
          { mem := st_p.mem, regs := Function.update r₅₀ 5 x, pos := st_p.pos } _ :=
        runs_assign_iff.mpr ⟨x, by simp [Expr.eval, r₅₀, hr₄_1], rfl, rfl, rfl⟩
      let r₅ := Function.update r₅₀ 5 x
      have hr₅_2 : r₅ 2 = nb + NODE_STRIDE * x := by simp [r₅, r₅₀, hr₄_2]
      have ha6 : Runs w p ω (Stmt.assign 6 (fieldLoadExpr 2 OFF_PPAR))
          { mem := st_p.mem, regs := r₅, pos := st_p.pos } .normal
          { mem := st_p.mem, regs := Function.update r₅ 6 (nodeField st_p.mem nb x OFF_PPAR), pos := st_p.pos } _ :=
        runs_assign_iff.mpr ⟨nodeField st_p.mem nb x OFF_PPAR,
          eval_fieldLoadExpr hr₅_2 hpp_lt, rfl, rfl, rfl⟩
      have hseq := runs_seq_normal hr2 (runs_seq_normal hr3 (runs_seq_normal hcond_then (runs_seq_normal ha5 ha6)))
      have hfr_all := lctFrame_trans hfr_0_ptr hfr_p
      have hhp₁ : st_p.mem (nb - 1) < 2 ^ w := by rw [hhp_ptr] at hhi_p; dsimp only [nb] at *; omega
      have hhpp_p : nodeField st_p.mem nb x OFF_PPAR = nodeField mem₀ nb x OFF_PPAR := by
        rw [hnonAgg_p OFF_PPAR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx_pp_eq]
      have hout_all : ∀ u ≤ cap, ∀ off < NODE_STRIDE, u ≠ x →
          (u = rc → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField st_p.mem nb u off = nodeField mem₀ nb u off := by
        intro u hu off hoff hux hurc
        have hout_addr := hout_p (nb + NODE_STRIDE * u + off)
          (by omega)
          (slot_disjoint_of_ne hux hoff)
          (by rw [hhp_ptr]; exact slot_lt_of_arena hu hoff harena₀)
        change nodeField st_p.mem nb u off = nodeField mem_ptr nb u off at hout_addr
        rw [hout_addr]
        refine hptr_field u off hoff ⟨fun h => hux h.1, fun h => (hurc h.1).2 h.2, fun h => (hurc h.1).1 h.2⟩
      have hnonAgg_x : ∀ off < NODE_STRIDE, off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
          off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
          off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
          off ≠ OFF_RIGHT → nodeField st_p.mem nb x off = nodeField mem₀ nb x off := by
        intro off hoff h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
        rw [hnonAgg_p off hoff h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
        exact hptr_field x off hoff ⟨fun h => h12 h.2, fun h => hx_ne_rc h.1, fun h => hx_ne_rc h.1⟩
      have hl_fields : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          nodeField st_p.mem nb u off = nodeField mem₀ nb u off := by
        intro u hu off hoff
        have hux : u ≠ x := fun h => hx_nin_l (h ▸ hu)
        have huc : u ≠ rc := fun h => by
          have hnd' := hnd_x; rw [AuxTree.toList, List.nodup_append] at hnd'
          exact hnd'.2.2 u (by simp [hu]) rc (by simp [hr_eq, AuxTree.toList]) h
        exact hout_all u (hx_tok.2.2.nodup_perm_mem (y := u) (by simp [AuxTree.toList, hu])).2
          off hoff hux (fun h => absurd h huc)
      have hl_out : ∀ u ≤ cap, u ∉ (AuxTree.node x l .leaf).toList → ∀ off < NODE_STRIDE,
          ((AuxTree.node rc rl rr) ≠ .leaf → u = (AuxTree.node rc rl rr).rootId →
            off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
          nodeField st_p.mem nb u off = nodeField mem₀ nb u off := by
        intro u hu hnin off hoff hurc
        exact hout_all u hu off hoff (fun h => hnin (by simp [AuxTree.toList, h]))
          (fun h => hurc (by simp) (by simpa [AuxTree.rootId] using h))
      have hr_par_p : (AuxTree.node rc rl rr) ≠ .leaf →
          nodeField st_p.mem nb (AuxTree.node rc rl rr).rootId OFF_PARENT = 0 := fun _ => by
        rw [show (AuxTree.node rc rl rr).rootId = rc from rfl]
        have hout_addr := hout_p (nb + NODE_STRIDE * rc + OFF_PARENT)
          (hnb1_ne_slot rc OFF_PARENT hrc_b.1 (by decide)).symm
          (slot_disjoint_of_ne hx_ne_rc.symm (by decide))
          (by rw [hhp_ptr]; exact slot_lt_of_arena hrc_b.2 (by decide) harena₀)
        change nodeField st_p.mem nb rc OFF_PARENT = nodeField mem_ptr nb rc OFF_PARENT at hout_addr
        rw [hout_addr, hrc_par_ptr]
      have hr_pp_p : (AuxTree.node rc rl rr) ≠ .leaf →
          nodeField st_p.mem nb (AuxTree.node rc rl rr).rootId OFF_PPAR = x := fun _ => by
        rw [show (AuxTree.node rc rl rr).rootId = rc from rfl]
        have hout_addr := hout_p (nb + NODE_STRIDE * rc + OFF_PPAR)
          (hnb1_ne_slot rc OFF_PPAR hrc_b.1 (by decide)).symm
          (slot_disjoint_of_ne hx_ne_rc.symm (by decide))
          (by rw [hhp_ptr]; exact slot_lt_of_arena hrc_b.2 (by decide) harena₀)
        change nodeField st_p.mem nb rc OFF_PPAR = nodeField mem_ptr nb rc OFF_PPAR at hout_addr
        rw [hout_addr, hrc_pp_ptr]
      have hdet := LctExposeInvs.of_detach (r := .node rc rl rr) (by simpa [hr_eq] using hi)
        hv hrev0 hht0 (by simpa [nb] using hhp₁) (by simpa [nb, x] using hhpp_p)
        (by simpa [nb, x, hhpp_p] using htm_p) (by simpa [nb] using hl_fields)
        (by simpa [nb, x] using hnonAgg_x) (by simpa [nb, x, cap] using hl_out)
        (by simpa [nb] using hr_par_p) (by simpa [nb, x] using hr_pp_p) hfr_all
      rcases hdet with ⟨hi₁, hpar_eq, hrep_eq, _, hphi_eq, hheavy_le, htop_sz⟩
      have hrev_x1 : revFlag st_p.mem nb x = false := by
        have hrv : nodeField st_p.mem nb x OFF_REV = 0 := by
          rw [hnonAgg_x OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrev0]
        simp [revFlag, hrv]
      have hlast_eq : ((AuxTree.node x l .leaf).evalInorder (revFlag st_p.mem nb) false).getLast? = some x := by
        simp [AuxTree.evalInorder, hrev_x1]
      have hnot : (AuxTree.node rc rl rr = AuxTree.leaf) = False := by simp
      have hphi_le : lctPhi L st_p.mem b n ≤ lctPhi L mem₀ b n + C_HEAVY L := by
        unfold lctPhi
        rw [hphi_eq]
        have hh1 : lctHeavyCount st_p.mem (lctNodesBase b) (lctCap n) ≤
            lctHeavyCount mem₀ (lctNodesBase b) (lctCap n) + 1 := by
          simp only [reduceCtorEq, ↓reduceIte] at hheavy_le; exact hheavy_le
        have hmul : C_HEAVY L * lctHeavyCount st_p.mem (lctNodesBase b) (lctCap n) ≤
            C_HEAVY L * lctHeavyCount mem₀ (lctNodesBase b) (lctCap n) + C_HEAVY L := by
          have := Nat.mul_le_mul_left (C_HEAVY L) hh1
          rwa [Nat.mul_add, Nat.mul_one] at this
        omega
      have hdiff_hp : st_p.mem (nb - 1) - mem₀ (nb - 1) = st_p.mem (nb - 1) - mem_ptr (nb - 1) := by
        rw [hhp_ptr]
      refine ⟨_, _, hseq, by simpa [trees₁, hr_eq, hnot] using hi₁, hsafe_p, hfr_all,
        hpar_eq, hrep_eq,
        by simp [r₅, r₅₀, hr₄_0], by simp [r₅, r₅₀, hr₄_1], by simp [r₅], by simp, hhpp_p,
        hlast_eq, by simpa [hr_eq] using htop_sz, ?_⟩
      simp only [Expr.size, nodePtrExpr, fieldLoadExpr, fieldAddrExpr] at *
      omega

end Phase1Execution

end MinCostFlow.LinkCut.Prog
