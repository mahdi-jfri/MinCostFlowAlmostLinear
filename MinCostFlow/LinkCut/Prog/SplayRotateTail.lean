module

public import MinCostFlow.LinkCut.Prog.SplayRotateBlocks

/-!
Post-rewiring tail execution `rotateTail_runs` for `rotateBody`:
completes parent/grandparent rewiring, invokes `pullBody` twice (first on `p_id`,
then on `x`), lifts the subtree `TreeMemMatch` and `evalMemSteps` across
`AuxTree.replaceSubtree_preserves`, and composes `LctFrame` with budget `2 * K_PULL L + 60`.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

@[expose] public section

private theorem nodeField_pres_pull {nodesBase cap x_pulled u off : ℕ}
    {mem₁ mem₂ : ℕ → ℕ}
    (hnb : 3 ≤ nodesBase) (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₁ (nodesBase - 1))
    (hu_le : u ≤ cap) (hux : u ≠ x_pulled) (hoff : off < NODE_STRIDE)
    (hpout : ∀ addr, addr ≠ nodesBase - 1 →
      (addr < nodesBase + NODE_STRIDE * x_pulled ∨
        nodesBase + NODE_STRIDE * x_pulled + NODE_STRIDE ≤ addr) →
      addr < mem₁ (nodesBase - 1) → mem₂ addr = mem₁ addr) :
    nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off := by
  apply hpout
  · exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.sub_lt (le_trans (by decide) hnb) (by decide)) (by omega))
  · exact node_field_addr_outside hux hoff
  · have hlt_ar : nodesBase + NODE_STRIDE * u + off < nodesBase + NODE_STRIDE * (cap + 1) := by
      unfold NODE_STRIDE at hoff ⊢; omega
    exact lt_of_lt_of_le hlt_ar harena

private theorem nodeNonStruct_pull_pres {nodesBase cap x_pulled u : ℕ}
    {mem₁ mem₂ : ℕ → ℕ}
    (hnb : 3 ≤ nodesBase) (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₁ (nodesBase - 1))
    (hu_le : u ≤ cap)
    (hpout : ∀ addr, addr ≠ nodesBase - 1 →
      (addr < nodesBase + NODE_STRIDE * x_pulled ∨
        nodesBase + NODE_STRIDE * x_pulled + NODE_STRIDE ≤ addr) →
      addr < mem₁ (nodesBase - 1) → mem₂ addr = mem₁ addr)
    (hpfields : ∀ off < NODE_STRIDE,
      off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
      off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
      nodeField mem₂ nodesBase x_pulled off = nodeField mem₁ nodesBase x_pulled off) :
    ∀ off, IsNonStructNonAggOff off →
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off := by
  intro off hoff
  by_cases hux : u = x_pulled
  · subst hux
    exact hpfields off hoff.1 hoff.2.2.2.2.2.1 hoff.2.2.2.2.2.2.1 hoff.2.2.2.2.2.2.2.1
      hoff.2.2.2.2.2.2.2.2.1 hoff.2.2.2.2.2.2.2.2.2.1 hoff.2.2.2.2.2.2.2.2.2.2.1
      hoff.2.2.2.2.2.2.2.2.2.2.2.1 hoff.2.2.2.2.2.2.2.2.2.2.2.2.1
      hoff.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hoff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hoff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · exact nodeField_pres_pull hnb harena hu_le hux hoff.1 hpout

private theorem frame_preserves_hdr_L {nodesBase cap : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hnb : 3 ≤ nodesBase)
    (hf : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₁ mem₂) :
    mem₂ (nodesBase - 3) = mem₁ (nodesBase - 3) := by
  refine hf.2.2.2.2.2 (nodesBase - 3) (Or.inl ⟨?_, ?_⟩)
  · have hlt : nodesBase - 3 < nodesBase := Nat.sub_lt (le_trans (by decide) hnb) (by decide)
    exact lt_of_lt_of_le hlt (Nat.le_add_right _ _)
  · omega

private theorem heap_agree_of_lctFrame {arenaHi lo hdrHeap : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hf : LctFrame lo arenaHi hdrHeap m₁ m₂) :
    ∀ a, arenaHi ≤ a → a < m₁ hdrHeap → m₂ a = m₁ a :=
  fun a ha1 ha2 => hf.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)

private theorem parent_child_field_of_ne_root {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p₀ pp₀ subId : ℕ}
    (ht : TreeMemMatch w h L mem nodesBase cap t p₀ pp₀)
    (hnd : t.toList.Nodup) (hsub : subId ∈ t.toList) (hne : subId ≠ t.rootId) :
    nodeField mem nodesBase (t.parentIn subId p₀) OFF_LEFT = subId ∨
    nodeField mem nodesBase (t.parentIn subId p₀) OFF_RIGHT = subId := by
  have hg_mem := (AuxTree.parentIn_mem_and_depth (p₀ := p₀) hnd hsub hne).1
  rcases AuxTree.parentIn_child_cases hnd hsub hne (rfl : t.parentIn subId p₀ = _) with
    ⟨gsl, gsr, hfind, hcas⟩
  have hm := AuxTree.findSubtree_match ht hg_mem
  rw [hfind] at hm
  rcases hm with ⟨_, _, hL, hR, _⟩
  rcases hcas with ⟨A, B, rfl⟩ | ⟨_, C, D, rfl⟩
  · exact Or.inl (by simpa [AuxTree.rootId] using hL)
  · exact Or.inr (by simpa [AuxTree.rootId] using hR)

theorem rotateTail_runs {w h L nodesBase cap x p_id g_id pp_p pp : ℕ}
    (pr : Program) (sp : SplayProcs) (mem₀ : ℕ → ℕ)
    (hp_ok : SplayProgramOk w h pr sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hhp_lt : mem₀ (nodesBase - 1) + 8 * L < 2 ^ w)
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree} (ht : TreeMemMatch w h L mem₀ nodesBase cap t 0 pp) (hnd : t.toList.Nodup)
    (hx_mem : x ∈ t.toList) (hx_ne_root : x ≠ t.rootId)
    (hp_def : p_id = t.parentIn x 0)
    (hg_def : g_id = t.parentIn p_id 0)
    (hpp_def : pp_p = if t.rootId = p_id then pp else 0)
    (st_mid : State)
    {xl xr pl pr_tree : AuxTree}
    (hshape :
      (xl = .node p_id pl pr_tree ∧
        nodeField st_mid.mem nodesBase x OFF_LEFT = p_id ∧
        nodeField st_mid.mem nodesBase x OFF_RIGHT = xr.rootId ∧
        TreeMemMatch w h L st_mid.mem nodesBase cap xr x 0) ∨
      (xr = .node p_id pl pr_tree ∧
        nodeField st_mid.mem nodesBase x OFF_LEFT = xl.rootId ∧
        nodeField st_mid.mem nodesBase x OFF_RIGHT = p_id ∧
        TreeMemMatch w h L st_mid.mem nodesBase cap xl x 0))
    (hs'_eq : (AuxTree.node x xl xr) = (t.findSubtree p_id).rotateAt x)
    (hs'_perm : (AuxTree.node x xl xr).toList.Perm (t.findSubtree p_id).toList)
    (hs'_eval : (AuxTree.node x xl xr).evalInorder (revFlag st_mid.mem nodesBase) false =
      (t.findSubtree p_id).evalInorder (revFlag mem₀ nodesBase) false)
    (hp_left : nodeField st_mid.mem nodesBase p_id OFF_LEFT = pl.rootId)
    (hp_right : nodeField st_mid.mem nodesBase p_id OFF_RIGHT = pr_tree.rootId)
    (hpl : TreeMemMatch w h L st_mid.mem nodesBase cap pl p_id 0)
    (hpr : TreeMemMatch w h L st_mid.mem nodesBase cap pr_tree p_id 0)
    (hx_ppar : nodeField st_mid.mem nodesBase x OFF_PPAR = pp_p)
    (hp_ppar : nodeField st_mid.mem nodesBase p_id OFF_PPAR = 0)
    (hx_rev0 : nodeField mem₀ nodesBase x OFF_REV = 0)
    (hp_rev0 : nodeField mem₀ nodesBase p_id OFF_REV = 0)
    (hx_ht0 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 0)
    (hp_ht0 : nodeField mem₀ nodesBase p_id OFF_HAS_TAG = 0)
    (hns_mid : ∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
      nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off)
    (hout_mid : ∀ u ≤ cap, u ∉ (t.findSubtree p_id).toList → ∀ off < NODE_STRIDE,
      nodeField st_mid.mem nodesBase u off = nodeField mem₀ nodesBase u off)
    (hpre_mid : MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      mem₀ st_mid.mem)
    (hr0 : st_mid.regs 0 = nodesBase)
    (hr1 : st_mid.regs 1 = x)
    (hr2 : st_mid.regs 2 = nodesBase + NODE_STRIDE * x)
    (hr3 : st_mid.regs 3 = p_id)
    (hr4 : st_mid.regs 4 = nodesBase + NODE_STRIDE * p_id)
    (hr5 : st_mid.regs 5 = g_id) :
    ∀ ω, ∃ st' c,
      Runs w pr ω
        (Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.reg 1) ;;
         Stmt.store (fieldAddrExpr 2 OFF_PARENT) (.reg 5) ;;
         Stmt.cond (.reg 5)
           (Stmt.assign 10 (nodePtrExpr 0 5) ;;
            Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
            Stmt.cond (.bin .eq (.reg 3) (.reg 11))
              (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
              (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1)))
           Stmt.nop ;;
         Stmt.call 11 sp.pull [.reg 0, .reg 3] ;;
         Stmt.call 11 sp.pull [.reg 0, .reg 1] ;;
         Stmt.ret (.const 0)) st_mid (.returned 0) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ 2 * K_PULL L + 60 ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L ∧
      TreeMemMatch w h L st'.mem nodesBase cap (t.rotateAt x) 0 pp ∧
      (t.rotateAt x).toList.Perm t.toList ∧
      (t.rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L (t.rotateAt x) false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem := by
  intro ω
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  have hw0 : (0 : ℕ) < 2 ^ w := Nat.pow_pos (by decide)
  have hhdr_lt : nodesBase - 1 < nodesBase + NODE_STRIDE := by unfold NODE_STRIDE; omega
  have hp_mem : p_id ∈ t.toList := hp_def ▸ (AuxTree.parentIn_mem_and_depth hnd hx_mem hx_ne_root).1
  have hsub_nd : (t.findSubtree p_id).toList.Nodup := AuxTree.findSubtree_nodup hnd
  have hs'_nd : (AuxTree.node x xl xr).toList.Nodup := hs'_perm.nodup_iff.2 hsub_nd
  rcases ht.nodup_perm_mem hx_mem with ⟨hx1, hx2⟩
  rcases ht.nodup_perm_mem hp_mem with ⟨hp1, hp2⟩
  let ptrX := nodesBase + NODE_STRIDE * x
  let ptrP := nodesBase + NODE_STRIDE * p_id
  have hal_p_par : ptrP + OFF_PARENT < 2 ^ w := nodeAddr_lt_pow hbase hp2 (by decide)
  have hal_x_par : ptrX + OFF_PARENT < 2 ^ w := nodeAddr_lt_pow hbase hx2 (by decide)
  let mem1 := Function.update st_mid.mem (ptrP + OFF_PARENT) x
  let st1 : State := { mem := mem1, regs := st_mid.regs, pos := st_mid.pos }
  let mem2 := Function.update mem1 (ptrX + OFF_PARENT) g_id
  let st2 : State := { mem := mem2, regs := st_mid.regs, pos := st_mid.pos }
  have hs_1 : Runs w pr ω (Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.reg 1)) st_mid .normal st1
      ((fieldAddrExpr 4 OFF_PARENT).size + (Expr.reg 1).size + 1) :=
    runs_store_iff.mpr ⟨ptrP + OFF_PARENT, x,
      eval_fieldAddrExpr hr4 hal_p_par, Expr.eval_reg_of_eq hr1, rfl, rfl, rfl⟩
  have hs_2 : Runs w pr ω (Stmt.store (fieldAddrExpr 2 OFF_PARENT) (.reg 5)) st1 .normal st2
      ((fieldAddrExpr 2 OFF_PARENT).size + (Expr.reg 5).size + 1) :=
    runs_store_iff.mpr ⟨ptrX + OFF_PARENT, g_id,
      eval_fieldAddrExpr hr2 hal_x_par, Expr.eval_reg_of_eq hr5, rfl, rfl, rfl⟩
  have hcond_step : ∃ st3 c_cond,
      Runs w pr ω
        (Stmt.cond (.reg 5)
          (Stmt.assign 10 (nodePtrExpr 0 5) ;;
           Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
           Stmt.cond (.bin .eq (.reg 3) (.reg 11))
             (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
             (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1)))
          Stmt.nop)
        st2 .normal st3 c_cond ∧
      c_cond ≤ 25 ∧
      st3.pos = st_mid.pos ∧
      st3.regs 0 = nodesBase ∧ st3.regs 1 = x ∧ st3.regs 3 = p_id ∧
      (g_id = 0 → st3.mem = mem2) ∧
      (g_id ≠ 0 → ∃ g_mem1,
        (g_mem1 = mem2 (nodesBase + NODE_STRIDE * g_id + OFF_LEFT) ∧
         (p_id = g_mem1 →
           st3.mem = Function.update mem2 (nodesBase + NODE_STRIDE * g_id + OFF_LEFT) x) ∧
         (p_id ≠ g_mem1 →
           st3.mem = Function.update mem2 (nodesBase + NODE_STRIDE * g_id + OFF_RIGHT) x))) := by
    by_cases hg0 : g_id = 0
    · refine ⟨st2, 1 + 1 + 1, ?_, by omega, rfl, hr0, hr1, hr3, fun _ => rfl, fun h => absurd hg0 h⟩
      exact runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (w := w) (by simpa [st2, hg0] using hr5),
        by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    · have hp_ne_root : p_id ≠ t.rootId := by
        intro h; rw [h] at hg_def
        have hne_t : t ≠ .leaf := fun hl => by simp [hl, AuxTree.toList] at hp_mem
        rw [AuxTree.parentIn_root hne_t] at hg_def; exact hg0 hg_def
      rcases AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hp_ne_root with ⟨hg_mem, _⟩
      rcases ht.nodup_perm_mem (hg_def ▸ hg_mem) with ⟨hg1, hg2⟩
      let ptrG := nodesBase + NODE_STRIDE * g_id
      have hg_ptr_lt : ptrG < 2 ^ w := nodePtr_lt_pow hbase hg2
      have hg_left_lt : ptrG + OFF_LEFT < 2 ^ w := nodeAddr_lt_pow hbase hg2 (by decide)
      have hg_right_lt : ptrG + OFF_RIGHT < 2 ^ w := nodeAddr_lt_pow hbase hg2 (by decide)
      let gLeft := mem2 (ptrG + OFF_LEFT)
      let st_g1 : State := { mem := mem2, regs := Function.update st2.regs 10 ptrG, pos := st_mid.pos }
      let st_g2 : State := { mem := mem2, regs := Function.update st_g1.regs 11 gLeft, pos := st_mid.pos }
      have ha_g1 : Runs w pr ω (Stmt.assign 10 (nodePtrExpr 0 5)) st2 .normal st_g1
          ((nodePtrExpr 0 5).size + 1) :=
        runs_assign_iff.mpr ⟨ptrG, eval_nodePtrExpr hstride hr0 hr5 hg_ptr_lt, rfl, rfl, rfl⟩
      have ha_g2 : Runs w pr ω (Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT)) st_g1 .normal st_g2
          ((fieldLoadExpr 10 OFF_LEFT).size + 1) :=
        runs_assign_iff.mpr ⟨gLeft, eval_fieldLoadExpr (by simp [st_g1]) hg_left_lt, rfl, rfl, rfl⟩
      have hcmp_eval : (Expr.bin .eq (.reg 3) (.reg 11)).eval w st_g2 =
          some (if p_id = gLeft then 1 else 0) :=
        Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [st_g2, st_g1, st2, hr3]))
          (Expr.eval_reg_of_eq (by simp [st_g2])) (by unfold NODE_STRIDE at hbase; omega)
      by_cases hgl : p_id = gLeft
      · let mem3 := Function.update mem2 (ptrG + OFF_LEFT) x
        let st3 : State := { mem := mem3, regs := st_g2.regs, pos := st_mid.pos }
        have hs_g3 : Runs w pr ω (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1)) st_g2 .normal st3
            ((fieldAddrExpr 10 OFF_LEFT).size + (Expr.reg 1).size + 1) :=
          runs_store_iff.mpr ⟨ptrG + OFF_LEFT, x,
            eval_fieldAddrExpr (by simp [st_g2, st_g1]) hg_left_lt,
            Expr.eval_reg_of_eq (by simp [st_g2, st_g1, st2, hr1]), rfl, rfl, rfl⟩
        have hif_inner : Runs w pr ω
            (Stmt.cond (.bin .eq (.reg 3) (.reg 11))
              (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
              (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1))) st_g2 .normal st3 _ :=
          runs_cond_iff.mpr ⟨1, _, by simpa [hgl] using hcmp_eval, by simpa using hs_g3, rfl⟩
        have hbody_g : Runs w pr ω
            (Stmt.assign 10 (nodePtrExpr 0 5) ;;
             Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
             Stmt.cond (.bin .eq (.reg 3) (.reg 11))
               (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
               (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1))) st2 .normal st3 _ :=
          runs_seq_iff.mpr (Or.inr ⟨st_g1, _, _, ha_g1,
            runs_seq_iff.mpr (Or.inr ⟨st_g2, _, _, ha_g2, hif_inner, rfl⟩), rfl⟩)
        refine ⟨st3, _, runs_cond_iff.mpr ⟨g_id, _, Expr.eval_reg_of_eq hr5,
          by simpa [hg0] using hbody_g, rfl⟩,
          (by simp [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size]), rfl,
          by simp [st3, st_g2, st_g1, st2, hr0],
          by simp [st3, st_g2, st_g1, st2, hr1],
          by simp [st3, st_g2, st_g1, st2, hr3],
          fun h => absurd h hg0,
          fun _ => ⟨gLeft, rfl, fun _ => rfl, fun h => absurd hgl h⟩⟩
      · let mem3 := Function.update mem2 (ptrG + OFF_RIGHT) x
        let st3 : State := { mem := mem3, regs := st_g2.regs, pos := st_mid.pos }
        have hs_g3 : Runs w pr ω (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1)) st_g2 .normal st3
            ((fieldAddrExpr 10 OFF_RIGHT).size + (Expr.reg 1).size + 1) :=
          runs_store_iff.mpr ⟨ptrG + OFF_RIGHT, x,
            eval_fieldAddrExpr (by simp [st_g2, st_g1]) hg_right_lt,
            Expr.eval_reg_of_eq (by simp [st_g2, st_g1, st2, hr1]), rfl, rfl, rfl⟩
        have hif_inner : Runs w pr ω
            (Stmt.cond (.bin .eq (.reg 3) (.reg 11))
              (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
              (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1))) st_g2 .normal st3 _ :=
          runs_cond_iff.mpr ⟨0, _, by simpa [hgl] using hcmp_eval, by simpa using hs_g3, rfl⟩
        have hbody_g : Runs w pr ω
            (Stmt.assign 10 (nodePtrExpr 0 5) ;;
             Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
             Stmt.cond (.bin .eq (.reg 3) (.reg 11))
               (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
               (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1))) st2 .normal st3 _ :=
          runs_seq_iff.mpr (Or.inr ⟨st_g1, _, _, ha_g1,
            runs_seq_iff.mpr (Or.inr ⟨st_g2, _, _, ha_g2, hif_inner, rfl⟩), rfl⟩)
        refine ⟨st3, _, runs_cond_iff.mpr ⟨g_id, _, Expr.eval_reg_of_eq hr5,
          by simpa [hg0] using hbody_g, rfl⟩,
          (by simp [nodePtrExpr, fieldLoadExpr, fieldAddrExpr, Expr.size]), rfl,
          by simp [st3, st_g2, st_g1, st2, hr0],
          by simp [st3, st_g2, st_g1, st2, hr1],
          by simp [st3, st_g2, st_g1, st2, hr3],
          fun h => absurd h hg0,
          fun _ => ⟨gLeft, rfl, fun h => absurd h hgl, fun _ => rfl⟩⟩
  rcases hcond_step with ⟨st3, c_cond, hr_cond, hc_cond, hpos3, hr3_0, hr3_1, hr3_3, hg_eq0, hg_ne0⟩
  have hsub_nd' := hs'_nd
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
    List.mem_singleton] at hsub_nd'
  rcases hsub_nd' with ⟨⟨hxl_nd, _, hdisj_xl_x⟩, hxr_nd, hdisj_sub⟩
  have hx_nin_xl : x ∉ xl.toList := fun h => hdisj_xl_x x h x rfl rfl
  have hx_nin_xr : x ∉ xr.toList := fun h => hdisj_sub x (Or.inr rfl) x h rfl
  have hx_ne_p : x ≠ p_id := by
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> intro h <;> subst h
    · exact hx_nin_xl (by simp [AuxTree.toList])
    · exact hx_nin_xr (by simp [AuxTree.toList])
  have hg_nin_s' : g_id ∉ (AuxTree.node x xl xr).toList := by
    by_cases hg0 : g_id = 0
    · intro h
      have := (ht.nodup_perm_mem (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 h))).1
      omega
    · have hp_ne_root : p_id ≠ t.rootId := by
        intro h; rw [h] at hg_def
        have hne_t : t ≠ .leaf := fun hl => by simp [hl, AuxTree.toList] at hp_mem
        rw [AuxTree.parentIn_root hne_t] at hg_def; exact hg0 hg_def
      rcases AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hp_ne_root with ⟨hg_mem, hg_dep, _⟩
      have hnin_sub := AuxTree.not_mem_findSubtree_of_ancestor hnd hg_mem hp_mem (by omega)
        (AuxTree.self_mem_pathTo hg_mem)
      rw [← hg_def] at hnin_sub
      exact fun h => hnin_sub (hs'_perm.mem_iff.1 h)
  have hp_nin_pl : p_id ∉ pl.toList := by
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hxl_nd
      exact fun h => hxl_nd.1.2.2 p_id h p_id rfl rfl
    · simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hxr_nd
      exact fun h => hxr_nd.1.2.2 p_id h p_id rfl rfl
  have hp_nin_pr : p_id ∉ pr_tree.toList := by
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hxl_nd
      exact fun h => hxl_nd.2.2 p_id (Or.inr rfl) p_id h rfl
    · simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hxr_nd
      exact fun h => hxr_nd.2.2 p_id (Or.inr rfl) p_id h rfl
  have hmem3_sub : ∀ u ∈ (AuxTree.node x xl xr).toList, ∀ off < NODE_STRIDE,
      (u = p_id → off ≠ OFF_PARENT) → (u = x → off ≠ OFF_PARENT) →
      nodeField st3.mem nodesBase u off = nodeField st_mid.mem nodesBase u off := by
    intro u hu off hoff hup hux
    have hu_neg : u ≠ g_id := fun h => hg_nin_s' (h ▸ hu)
    have hneq_gL : nodesBase + NODE_STRIDE * u + off ≠ nodesBase + NODE_STRIDE * g_id + OFF_LEFT :=
      node_field_addr_ne hu_neg hoff (by decide)
    have hneq_gR : nodesBase + NODE_STRIDE * u + off ≠ nodesBase + NODE_STRIDE * g_id + OFF_RIGHT :=
      node_field_addr_ne hu_neg hoff (by decide)
    have h32 : st3.mem (nodesBase + NODE_STRIDE * u + off) = mem2 (nodesBase + NODE_STRIDE * u + off) := by
      by_cases hg0 : g_id = 0
      · rw [hg_eq0 hg0]
      · rcases hg_ne0 hg0 with ⟨gL, _, hL, hR⟩
        by_cases hgl : p_id = gL
        · rw [hL hgl, Function.update_of_ne hneq_gL]
        · rw [hR hgl, Function.update_of_ne hneq_gR]
    have h21 : mem2 (nodesBase + NODE_STRIDE * u + off) = mem1 (nodesBase + NODE_STRIDE * u + off) := by
      dsimp only [mem2, ptrX]
      apply Function.update_of_ne
      by_cases he : u = x
      · subst he; intro h; exact hux rfl (Nat.add_left_cancel h)
      · exact node_field_addr_ne (off2 := OFF_PARENT) he hoff (by decide)
    have h10 : mem1 (nodesBase + NODE_STRIDE * u + off) = st_mid.mem (nodesBase + NODE_STRIDE * u + off) := by
      dsimp only [mem1, ptrP]
      apply Function.update_of_ne
      by_cases he : u = p_id
      · subst he; intro h; exact hup rfl (Nat.add_left_cancel h)
      · exact node_field_addr_ne (off2 := OFF_PARENT) he hoff (by decide)
    dsimp only [nodeField]; rw [h32, h21, h10]
  have hmem3_out : ∀ u ∉ (AuxTree.node x xl xr).toList, ∀ off < NODE_STRIDE,
      (g_id ≠ 0 → u = g_id → off ≠ OFF_LEFT ∧ off ≠ OFF_RIGHT) →
      nodeField st3.mem nodesBase u off = st_mid.mem (nodesBase + NODE_STRIDE * u + off) := by
    intro u hu off hoff hug
    have hux : u ≠ x := fun h => hu (by subst h; simp [AuxTree.toList])
    have hup : u ≠ p_id := by
      intro h; subst h; apply hu
      rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [AuxTree.toList]
    have h32 : st3.mem (nodesBase + NODE_STRIDE * u + off) = mem2 (nodesBase + NODE_STRIDE * u + off) := by
      by_cases hg0 : g_id = 0
      · rw [hg_eq0 hg0]
      · rcases hg_ne0 hg0 with ⟨gL, _, hL, hR⟩
        by_cases hug_eq : u = g_id
        · subst hug_eq
          have hne := hug hg0 rfl
          by_cases hgl : p_id = gL
          · rw [hL hgl, Function.update_of_ne (fun he => hne.1 (Nat.add_left_cancel he))]
          · rw [hR hgl, Function.update_of_ne (fun he => hne.2 (Nat.add_left_cancel he))]
        · by_cases hgl : p_id = gL
          · rw [hL hgl, Function.update_of_ne (node_field_addr_ne hug_eq hoff (by decide))]
          · rw [hR hgl, Function.update_of_ne (node_field_addr_ne hug_eq hoff (by decide))]
    have h21 : mem2 (nodesBase + NODE_STRIDE * u + off) = mem1 (nodesBase + NODE_STRIDE * u + off) := by
      dsimp only [mem2, ptrX]
      exact Function.update_of_ne (node_field_addr_ne (off2 := OFF_PARENT) hux hoff (by decide)) _ _
    have h10 : mem1 (nodesBase + NODE_STRIDE * u + off) = st_mid.mem (nodesBase + NODE_STRIDE * u + off) := by
      dsimp only [mem1, ptrP]
      exact Function.update_of_ne (node_field_addr_ne (off2 := OFF_PARENT) hup hoff (by decide)) _ _
    dsimp only [nodeField]; rw [h32, h21, h10]
  have hpre3 : MemPreservedOutside (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      mem₀ st3.mem := by
    apply memPreservedOutside_trans hpre_mid
    intro addr haddr
    have ha_p : addr ≠ ptrP + OFF_PARENT := by
      have : OFF_PARENT < NODE_STRIDE := by decide
      simp only [ptrP, NODE_STRIDE] at *; rcases haddr with h | h <;> omega
    have ha_x : addr ≠ ptrX + OFF_PARENT := by
      have : OFF_PARENT < NODE_STRIDE := by decide
      simp only [ptrX, NODE_STRIDE] at *; rcases haddr with h | h <;> omega
    have h32 : st3.mem addr = mem2 addr := by
      by_cases hg0 : g_id = 0
      · rw [hg_eq0 hg0]
      · have hp_ne_root : p_id ≠ t.rootId := by
          intro h; rw [h] at hg_def
          have hne_t : t ≠ .leaf := fun hl => by simp [hl, AuxTree.toList] at hp_mem
          rw [AuxTree.parentIn_root hne_t] at hg_def; exact hg0 hg_def
        rcases AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hp_ne_root with ⟨hg_mem, _⟩
        rcases ht.nodup_perm_mem (hg_def ▸ hg_mem) with ⟨hg1, hg2⟩
        have ha_g : ∀ o2 < NODE_STRIDE, addr ≠ nodesBase + NODE_STRIDE * g_id + o2 := fun o2 ho2 => by
          simp only [NODE_STRIDE] at ho2 haddr ⊢; rcases haddr with h | h <;> omega
        rcases hg_ne0 hg0 with ⟨gL, _, hL, hR⟩
        by_cases hgl : p_id = gL
        · rw [hL hgl, Function.update_of_ne (ha_g OFF_LEFT (by decide))]
        · rw [hR hgl, Function.update_of_ne (ha_g OFF_RIGHT (by decide))]
    have h21 : mem2 addr = mem1 addr := by dsimp only [mem2]; exact Function.update_of_ne ha_x _ _
    have h10 : mem1 addr = st_mid.mem addr := by dsimp only [mem1]; exact Function.update_of_ne ha_p _ _
    rw [h32, h21, h10]
  have hlct03 : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₀ st3.mem :=
    lctFrame_of_memPreservedOutside hpre3 hhdr_lt harena hz
  have hhp3_eq : st3.mem (nodesBase - 1) = mem₀ (nodesBase - 1) :=
    hpre3 (nodesBase - 1) (Or.inl hhdr_lt)
  have hL_hdr3 : st3.mem (nodesBase - 3) = L := (frame_preserves_hdr_L hnb hlct03).trans hL_hdr
  have harena3 : nodesBase + NODE_STRIDE * (cap + 1) ≤ st3.mem (nodesBase - 1) := by
    rw [hhp3_eq]; exact harena
  have hz3 : ZeroFrom st3.mem (st3.mem (nodesBase - 1)) := hlct03.2.2.2.2.1
  have h0_3 : SlotZeroOk st3.mem nodesBase :=
    memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct03
  have hag30 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
      st3.mem a = mem₀ a := heap_agree_of_lctFrame hlct03
  have hns3 : ∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
      nodeField st3.mem nodesBase u off = nodeField mem₀ nodesBase u off := by
    intro u hu off hoff
    rw [← hns_mid u hu off hoff]
    have h32 : st3.mem (nodesBase + NODE_STRIDE * u + off) = mem2 (nodesBase + NODE_STRIDE * u + off) := by
      by_cases hg0 : g_id = 0
      · rw [hg_eq0 hg0]
      · rcases hg_ne0 hg0 with ⟨gL, _, hL, hR⟩
        by_cases hgl : p_id = gL
        · rw [hL hgl]
          by_cases huy : u = g_id
          · subst huy; exact Function.update_of_ne (node_same_field_addr_ne hoff.2.1) _ _
          · exact Function.update_of_ne (node_field_addr_ne huy hoff.1 (by decide)) _ _
        · rw [hR hgl]
          by_cases huy : u = g_id
          · subst huy; exact Function.update_of_ne (node_same_field_addr_ne hoff.2.2.1) _ _
          · exact Function.update_of_ne (node_field_addr_ne huy hoff.1 (by decide)) _ _
    have h21 : mem2 (nodesBase + NODE_STRIDE * u + off) = mem1 (nodesBase + NODE_STRIDE * u + off) := by
      dsimp only [mem2, ptrX]
      by_cases huy : u = x
      · subst huy; exact Function.update_of_ne (node_same_field_addr_ne hoff.2.2.2.1) _ _
      · exact Function.update_of_ne (node_field_addr_ne huy hoff.1 (by decide)) _ _
    have h10 : mem1 (nodesBase + NODE_STRIDE * u + off) = st_mid.mem (nodesBase + NODE_STRIDE * u + off) := by
      dsimp only [mem1, ptrP]
      by_cases huy : u = p_id
      · subst huy; exact Function.update_of_ne (node_same_field_addr_ne hoff.2.2.2.1) _ _
      · exact Function.update_of_ne (node_field_addr_ne huy hoff.1 (by decide)) _ _
    dsimp only [nodeField]; rw [h32, h21, h10]
  have hp_par3 : nodeField st3.mem nodesBase p_id OFF_PARENT = x := by
    have h_g_ne_p : g_id ≠ p_id := fun h => hg_nin_s' (h ▸ by rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [AuxTree.toList])
    have h32 : st3.mem (ptrP + OFF_PARENT) = mem2 (ptrP + OFF_PARENT) := by
      by_cases hg0 : g_id = 0
      · rw [hg_eq0 hg0]
      · rcases hg_ne0 hg0 with ⟨gL, _, hL, hR⟩
        by_cases hgl : p_id = gL
        · rw [hL hgl, Function.update_of_ne (node_field_addr_ne h_g_ne_p.symm (by decide) (by decide))]
        · rw [hR hgl, Function.update_of_ne (node_field_addr_ne h_g_ne_p.symm (by decide) (by decide))]
    have h21 : mem2 (ptrP + OFF_PARENT) = mem1 (ptrP + OFF_PARENT) := by
      dsimp only [mem2, ptrX, ptrP]
      exact Function.update_of_ne (node_field_addr_ne hx_ne_p.symm (by decide) (by decide)) _ _
    dsimp only [nodeField]; change st3.mem (ptrP + OFF_PARENT) = x
    rw [h32, h21]; dsimp only [mem1]; rw [Function.update_self]
  have hx_par3 : nodeField st3.mem nodesBase x OFF_PARENT = g_id := by
    have h_g_ne_x : g_id ≠ x := fun h => hg_nin_s' (h ▸ by simp [AuxTree.toList])
    have h32 : st3.mem (ptrX + OFF_PARENT) = mem2 (ptrX + OFF_PARENT) := by
      by_cases hg0 : g_id = 0
      · rw [hg_eq0 hg0]
      · rcases hg_ne0 hg0 with ⟨gL, _, hL, hR⟩
        by_cases hgl : p_id = gL
        · rw [hL hgl, Function.update_of_ne (node_field_addr_ne h_g_ne_x.symm (by decide) (by decide))]
        · rw [hR hgl, Function.update_of_ne (node_field_addr_ne h_g_ne_x.symm (by decide) (by decide))]
    dsimp only [nodeField]; change st3.mem (ptrX + OFF_PARENT) = g_id
    rw [h32]; dsimp only [mem2]; rw [Function.update_self]
  have hp_in_s' : p_id ∈ (AuxTree.node x xl xr).toList := by
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [AuxTree.toList]
  have hpl_in_s' : ∀ u ∈ pl.toList, u ∈ (AuxTree.node x xl xr).toList ∧ u ≠ p_id ∧ u ≠ x := by
    intro u hu
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · refine ⟨by simp [AuxTree.toList, hu], fun h => hp_nin_pl (h ▸ hu),
        fun h => hx_nin_xl (h ▸ by simp [AuxTree.toList, hu])⟩
    · refine ⟨by simp [AuxTree.toList, hu], fun h => hp_nin_pl (h ▸ hu),
        fun h => hx_nin_xr (h ▸ by simp [AuxTree.toList, hu])⟩
  have hpr_in_s' : ∀ u ∈ pr_tree.toList, u ∈ (AuxTree.node x xl xr).toList ∧ u ≠ p_id ∧ u ≠ x := by
    intro u hu
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · refine ⟨by simp [AuxTree.toList, hu], fun h => hp_nin_pr (h ▸ hu),
        fun h => hx_nin_xl (h ▸ by simp [AuxTree.toList, hu])⟩
    · refine ⟨by simp [AuxTree.toList, hu], fun h => hp_nin_pr (h ▸ hu),
        fun h => hx_nin_xr (h ▸ by simp [AuxTree.toList, hu])⟩
  have hmid_eq0_heap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a →
      a < st_mid.mem (nodesBase - 1) → st3.mem a = st_mid.mem a := fun a ha1 ha2 => by
    have hm_hp : st_mid.mem (nodesBase - 1) = mem₀ (nodesBase - 1) := hpre_mid (nodesBase - 1) (Or.inl hhdr_lt)
    rw [hm_hp] at ha2
    exact (hag30 a ha1 ha2).trans (hpre_mid a (Or.inr ha1)).symm
  have hmid_le3 : st_mid.mem (nodesBase - 1) ≤ st3.mem (nodesBase - 1) := by
    rw [hhp3_eq, hpre_mid (nodesBase - 1) (Or.inl hhdr_lt)]
  have hpl3 : TreeMemMatch w h L st3.mem nodesBase cap pl p_id 0 :=
    memAgree_treeMemMatch_of_nodeList hpl (fun u hu off hoff =>
      hmem3_sub u (hpl_in_s' u hu).1 off hoff (fun h => absurd h (hpl_in_s' u hu).2.1)
        (fun h => absurd h (hpl_in_s' u hu).2.2)) hmid_le3 hmid_eq0_heap
  have hpr3 : TreeMemMatch w h L st3.mem nodesBase cap pr_tree p_id 0 :=
    memAgree_treeMemMatch_of_nodeList hpr (fun u hu off hoff =>
      hmem3_sub u (hpr_in_s' u hu).1 off hoff (fun h => absurd h (hpr_in_s' u hu).2.1)
        (fun h => absurd h (hpr_in_s' u hu).2.2)) hmid_le3 hmid_eq0_heap
  have hp_seq_vcnt : listVcnt st3.mem nodesBase
      (pl.evalInorder (revFlag st3.mem nodesBase) false ++ [p_id] ++
        pr_tree.evalInorder (revFlag st3.mem nodesBase) false) < 2 ^ w := by
    have hp_rev3 : revFlag st3.mem nodesBase p_id = false := by
      simp [revFlag, hns3 p_id hp2 OFF_REV (by decide), hp_rev0]
    have hnode_eq : (AuxTree.node p_id pl pr_tree).evalInorder (revFlag st3.mem nodesBase) false =
        pl.evalInorder (revFlag st3.mem nodesBase) false ++ [p_id] ++
          pr_tree.evalInorder (revFlag st3.mem nodesBase) false := by
      simp [AuxTree.evalInorder, hp_rev3]
    have hsub_toList : ∀ u ∈ (AuxTree.node p_id pl pr_tree).toList, u ∈ (AuxTree.node x xl xr).toList := by
      intro u hu
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rcases hu with (h | rfl) | h <;> simp [AuxTree.toList, *]
    have hnd_p : (AuxTree.node p_id pl pr_tree).toList.Nodup := by
      rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact hxl_nd; exact hxr_nd]
    have hperm_p := (AuxTree.node p_id pl pr_tree).evalInorder_perm (revFlag st3.mem nodesBase) false
    rw [← hnode_eq]
    apply listVcnt_lt_pow_of_le hbase (hperm_p.nodup_iff.2 hnd_p)
    · intro u hu
      exact ht.nodup_perm_mem (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 (hsub_toList u (hperm_p.mem_iff.1 hu))))
    · intro u hu
      have hu_t := AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 (hsub_toList u (hperm_p.mem_iff.1 hu)))
      rw [hns3 u (ht.nodup_perm_mem hu_t).2 OFF_ISV (by decide)]
      exact listIsv_bound_of_tree ht hu_t
  have hpre_p : PullPre w h L st3.mem nodesBase cap p_id pl pr_tree x 0 :=
    pullPre_of_nonStruct_agree ht hp_mem (by rw [hhp3_eq]) hag30 (hns3 p_id hp2)
      (by rw [hmem3_sub p_id hp_in_s' OFF_LEFT (by decide) (fun _ => by decide) (fun h => absurd h.symm hx_ne_p)]; exact hp_left)
      (by rw [hmem3_sub p_id hp_in_s' OFF_RIGHT (by decide) (fun _ => by decide) (fun h => absurd h.symm hx_ne_p)]; exact hp_right)
      hp_par3
      (by rw [hmem3_sub p_id hp_in_s' OFF_PPAR (by decide) (fun _ => by decide) (fun h => absurd h.symm hx_ne_p)]; exact hp_ppar)
      hp_rev0 hp_ht0 hpl3 hpr3 hp_seq_vcnt
  have hhp3_lt4L : st3.mem (nodesBase - 1) + 4 * L < 2 ^ w := by rw [hhp3_eq]; omega
  rcases pullBody_runs pr sp st3.mem st3.pos hp_ok hbase hnb hL_hdr3 harena3 hz3 hhp3_lt4L h0_3
      hp_nin_pl hp_nin_pr hpre_p ω with
    ⟨st4_call, c4, hr_p4, hc4, hhp4_ge, hhp4_le, hp_match4, hp_out4, hp_fields4, hlct34⟩
  let st4 : State := { st4_call with regs := Function.update st3.regs 11 0 }
  have hcall_p4 : Runs w pr ω (Stmt.call 11 sp.pull [.reg 0, .reg 3]) st3 .normal st4
      (2 + c4 + 1) := by
    have hargs4 : evalArgs w st3 [.reg 0, .reg 3] = some [nodesBase, p_id] := by
      simp [evalArgs, Expr.eval, hr3_0, hr3_3]
    exact runs_call_iff.mpr ⟨[nodesBase, p_id], pullBody sp, .returned 0, st4_call, c4,
      hargs4, hp_ok.pull_eq, hr_p4, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hlct04 : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₀ st4.mem := lctFrame_trans hlct03 hlct34
  have hL_hdr4 : st4.mem (nodesBase - 3) = L := (frame_preserves_hdr_L hnb hlct04).trans hL_hdr
  have harena4 : nodesBase + NODE_STRIDE * (cap + 1) ≤ st4.mem (nodesBase - 1) :=
    le_trans harena3 hhp4_ge
  have hz4 : ZeroFrom st4.mem (st4.mem (nodesBase - 1)) := hlct04.2.2.2.2.1
  have h0_4 : SlotZeroOk st4.mem nodesBase :=
    memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct04
  have hag40 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
      st4.mem a = mem₀ a := heap_agree_of_lctFrame hlct04
  have hhp4_lt4L : st4.mem (nodesBase - 1) + 4 * L < 2 ^ w := by
    change st4_call.mem (nodesBase - 1) + 4 * L < 2 ^ w
    rw [hhp3_eq] at hhp4_le
    omega
  have h4_eq3_outside_p : ∀ u ≤ cap, u ≠ p_id → ∀ off < NODE_STRIDE,
      nodeField st4.mem nodesBase u off = nodeField st3.mem nodesBase u off := fun u hu hup off hoff =>
    nodeField_pres_pull hnb harena3 hu hup hoff hp_out4
  have hns4 : ∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
      nodeField st4.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu off hoff =>
    (nodeNonStruct_pull_pres hnb harena3 hu hp_out4 hp_fields4 off hoff).trans (hns3 u hu off hoff)
  have hmid_eq4_heap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a →
      a < st_mid.mem (nodesBase - 1) → st4.mem a = st_mid.mem a := fun a ha1 ha2 => by
    have hm_hp : st_mid.mem (nodesBase - 1) = mem₀ (nodesBase - 1) := hpre_mid (nodesBase - 1) (Or.inl hhdr_lt)
    rw [hm_hp] at ha2
    exact (hag40 a ha1 ha2).trans (hpre_mid a (Or.inr ha1)).symm
  have hmid_le4 : st_mid.mem (nodesBase - 1) ≤ st4.mem (nodesBase - 1) := by
    rw [hpre_mid (nodesBase - 1) (Or.inl hhdr_lt), ← hhp3_eq]; exact hhp4_ge
  have hxl4 : TreeMemMatch w h L st4.mem nodesBase cap xl x 0 := by
    rcases hshape with ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, hxl_mid⟩
    · exact hp_match4
    · have hp_nin_xl : p_id ∉ xl.toList := fun h =>
        hdisj_sub p_id (Or.inl h) p_id (by simp [AuxTree.toList]) rfl
      refine memAgree_treeMemMatch_of_nodeList hxl_mid (fun u hu off hoff => ?_) hmid_le4 hmid_eq4_heap
      have hu_s' : u ∈ (AuxTree.node x xl (AuxTree.node p_id pl pr_tree)).toList := by
        simp [AuxTree.toList, hu]
      have hu_t := AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 hu_s')
      have hu_le : u ≤ cap := (ht.nodup_perm_mem hu_t).2
      have hup : u ≠ p_id := fun h => hp_nin_xl (h ▸ hu)
      have hux : u ≠ x := fun h => hx_nin_xl (h ▸ hu)
      rw [h4_eq3_outside_p u hu_le hup off hoff]
      exact hmem3_sub u hu_s' off hoff (fun h => absurd h hup) (fun h => absurd h hux)
  have hxr4 : TreeMemMatch w h L st4.mem nodesBase cap xr x 0 := by
    rcases hshape with ⟨rfl, _, _, hxr_mid⟩ | ⟨rfl, _, _, _⟩
    · have hp_nin_xr : p_id ∉ xr.toList := fun h =>
        hdisj_sub p_id (Or.inl (by simp [AuxTree.toList])) p_id h rfl
      refine memAgree_treeMemMatch_of_nodeList hxr_mid (fun u hu off hoff => ?_) hmid_le4 hmid_eq4_heap
      have hu_s' : u ∈ (AuxTree.node x (AuxTree.node p_id pl pr_tree) xr).toList := by
        simp [AuxTree.toList, hu]
      have hu_t := AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 hu_s')
      have hu_le : u ≤ cap := (ht.nodup_perm_mem hu_t).2
      have hup : u ≠ p_id := fun h => hp_nin_xr (h ▸ hu)
      have hux : u ≠ x := fun h => hx_nin_xr (h ▸ hu)
      rw [h4_eq3_outside_p u hu_le hup off hoff]
      exact hmem3_sub u hu_s' off hoff (fun h => absurd h hup) (fun h => absurd h hux)
    · exact hp_match4
  have hx_in_s' : x ∈ (AuxTree.node x xl xr).toList := by simp [AuxTree.toList]
  have hx_left4 : nodeField st4.mem nodesBase x OFF_LEFT = xl.rootId := by
    rw [h4_eq3_outside_p x hx2 hx_ne_p OFF_LEFT (by decide)]
    rw [hmem3_sub x hx_in_s' OFF_LEFT (by decide) (fun h => absurd h hx_ne_p) (fun _ => by decide)]
    rcases hshape with ⟨rfl, hL, _⟩ | ⟨_, hL, _⟩ <;> [simpa [AuxTree.rootId] using hL; exact hL]
  have hx_right4 : nodeField st4.mem nodesBase x OFF_RIGHT = xr.rootId := by
    rw [h4_eq3_outside_p x hx2 hx_ne_p OFF_RIGHT (by decide)]
    rw [hmem3_sub x hx_in_s' OFF_RIGHT (by decide) (fun h => absurd h hx_ne_p) (fun _ => by decide)]
    rcases hshape with ⟨_, _, hR, _⟩ | ⟨rfl, _, hR, _⟩ <;> [exact hR; simpa [AuxTree.rootId] using hR]
  have hx_par4 : nodeField st4.mem nodesBase x OFF_PARENT = g_id := by
    rw [h4_eq3_outside_p x hx2 hx_ne_p OFF_PARENT (by decide)]; exact hx_par3
  have hx_ppar4 : nodeField st4.mem nodesBase x OFF_PPAR = pp_p := by
    rw [h4_eq3_outside_p x hx2 hx_ne_p OFF_PPAR (by decide)]
    rw [hmem3_sub x hx_in_s' OFF_PPAR (by decide) (fun h => absurd h hx_ne_p) (fun _ => by decide)]
    exact hx_ppar
  have hx_seq_vcnt4 : listVcnt st4.mem nodesBase
      (xl.evalInorder (revFlag st4.mem nodesBase) false ++ [x] ++
        xr.evalInorder (revFlag st4.mem nodesBase) false) < 2 ^ w := by
    have hx_rev4 : revFlag st4.mem nodesBase x = false := by
      simp [revFlag, hns4 x hx2 OFF_REV (by decide), hx_rev0]
    have hnode_eq : (AuxTree.node x xl xr).evalInorder (revFlag st4.mem nodesBase) false =
        xl.evalInorder (revFlag st4.mem nodesBase) false ++ [x] ++
          xr.evalInorder (revFlag st4.mem nodesBase) false := by
      simp [AuxTree.evalInorder, hx_rev4]
    have hperm_x := (AuxTree.node x xl xr).evalInorder_perm (revFlag st4.mem nodesBase) false
    rw [← hnode_eq]
    apply listVcnt_lt_pow_of_le hbase (hperm_x.nodup_iff.2 hs'_nd)
    · intro u hu
      exact ht.nodup_perm_mem (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 (hperm_x.mem_iff.1 hu)))
    · intro u hu
      have hu_t := AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 (hperm_x.mem_iff.1 hu))
      rw [hns4 u (ht.nodup_perm_mem hu_t).2 OFF_ISV (by decide)]
      exact listIsv_bound_of_tree ht hu_t
  have hpre_x : PullPre w h L st4.mem nodesBase cap x xl xr g_id pp_p :=
    pullPre_of_nonStruct_agree ht hx_mem (by rw [← hhp3_eq]; exact hhp4_ge) hag40 (hns4 x hx2)
      hx_left4 hx_right4 hx_par4 hx_ppar4 hx_rev0 hx_ht0 hxl4 hxr4 hx_seq_vcnt4
  rcases pullBody_runs pr sp st4.mem st4.pos hp_ok hbase hnb hL_hdr4 harena4 hz4 hhp4_lt4L h0_4
      hx_nin_xl hx_nin_xr hpre_x ω with
    ⟨st5_call, c5, hr_x5, hc5, hhp5_ge, hhp5_le, hx_match5, hx_out5, hx_fields5, hlct45⟩
  let st5 : State := { st5_call with regs := Function.update st4.regs 11 0 }
  have hcall_x5 : Runs w pr ω (Stmt.call 11 sp.pull [.reg 0, .reg 1]) st4 .normal st5
      (2 + c5 + 1) := by
    have hargs5 : evalArgs w st4 [.reg 0, .reg 1] = some [nodesBase, x] := by
      have hr4_0 : st4.regs 0 = nodesBase := by simp [st4, hr3_0]
      have hr4_1 : st4.regs 1 = x := by simp [st4, hr3_1]
      simp [evalArgs, Expr.eval, hr4_0, hr4_1]
    exact runs_call_iff.mpr ⟨[nodesBase, x], pullBody sp, .returned 0, st5_call, c5,
      hargs5, hp_ok.pull_eq, hr_x5, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hret : Runs w pr ω (Stmt.ret (.const 0)) st5 (.returned 0) st5 ((Expr.const 0).size + 1) :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
  have hruns_all : Runs w pr ω
      (Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.reg 1) ;;
       Stmt.store (fieldAddrExpr 2 OFF_PARENT) (.reg 5) ;;
       Stmt.cond (.reg 5)
         (Stmt.assign 10 (nodePtrExpr 0 5) ;;
          Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
          Stmt.cond (.bin .eq (.reg 3) (.reg 11))
            (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
            (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1)))
         Stmt.nop ;;
       Stmt.call 11 sp.pull [.reg 0, .reg 3] ;;
       Stmt.call 11 sp.pull [.reg 0, .reg 1] ;;
       Stmt.ret (.const 0))
      st_mid (.returned 0) st5
      (5 + (5 + (c_cond + ((2 + c4 + 1) + ((2 + c5 + 1) + ((Expr.const 0).size + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, _, _, by simpa [fieldAddrExpr, Expr.size] using hs_1,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, by simpa [fieldAddrExpr, Expr.size] using hs_2,
        runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hr_cond,
          runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcall_p4,
            runs_seq_iff.mpr (Or.inr ⟨st5, _, _, hcall_x5, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hlct05 : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₀ st5.mem := lctFrame_trans hlct04 hlct45
  have hag50 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
      st5.mem a = mem₀ a := heap_agree_of_lctFrame hlct05
  have h5_eq4_outside_x : ∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField st5.mem nodesBase u off = nodeField st4.mem nodesBase u off := fun u hu hux off hoff =>
    nodeField_pres_pull hnb harena4 hu hux hoff hx_out5
  have hns5 : ∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
      nodeField st5.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu off hoff =>
    (nodeNonStruct_pull_pres hnb harena4 hu hx_out5 hx_fields5 off hoff).trans (hns4 u hu off hoff)
  let s' := AuxTree.node x xl xr
  have hs'_sub_rev5 : ∀ u ∈ s'.toList,
      nodeField st5.mem nodesBase u OFF_REV = nodeField st_mid.mem nodesBase u OFF_REV := fun u hu => by
    have hu_le := (ht.nodup_perm_mem (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 hu))).2
    exact (hns5 u hu_le OFF_REV (by decide)).trans (hns_mid u hu_le OFF_REV (by decide)).symm
  have hs'_eval5 : s'.evalInorder (revFlag st5.mem nodesBase) false =
      (t.findSubtree p_id).evalInorder (revFlag mem₀ nodesBase) false := by
    rw [evalInorder_agree_of_list hs'_sub_rev5 false]; exact hs'_eval
  have hvcnt_5 : listVcnt st5.mem nodesBase (s'.evalInorder (revFlag st5.mem nodesBase) false) =
      listVcnt mem₀ nodesBase ((t.findSubtree p_id).evalInorder (revFlag mem₀ nodesBase) false) := by
    rw [hs'_eval5]
    refine listVcnt_agree_of_mem fun u hu => ?_
    have hu_sub := (AuxTree.evalInorder_perm (revFlag mem₀ nodesBase) (t.findSubtree p_id) false).mem_iff.1 hu
    exact hns5 u (ht.nodup_perm_mem (AuxTree.findSubtree_subset hu_sub)).2 OFF_ISV (by decide)
  have hsteps_5 : evalMemSteps st5.mem nodesBase h L s' false 0 =
      evalMemSteps mem₀ nodesBase h L (t.findSubtree p_id) false 0 := by
    have hns_ok_s' : ∀ u ∈ s'.toList,
        NodeNonStructOk h L (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) nodesBase mem₀ u :=
      fun u hu => ht.nodeNonStructOk (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 hu))
    have hns5_s' : ∀ u ∈ s'.toList, ∀ off, IsNonStructNonAggOff off →
        nodeField st5.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu =>
      hns5 u (ht.nodup_perm_mem (AuxTree.findSubtree_subset (hs'_perm.mem_iff.1 hu))).2
    rw [evalMemSteps_agree_nonStruct hns_ok_s' hns5_s' hag50]
    rcases AuxTree.parentIn_child_cases hnd hx_mem hx_ne_root hp_def with ⟨sl, sr, hfind_p, hcas⟩
    have hrev_p0 : revFlag mem₀ nodesBase p_id = false := by simp [revFlag, hp_rev0]
    have hrev_x0 : revFlag mem₀ nodesBase x = false := by simp [revFlag, hx_rev0]
    rcases hcas with ⟨A, B, rfl⟩ | ⟨hsl_cond, C, D, rfl⟩
    · have hs'_rot : s' = AuxTree.node x A (AuxTree.node p_id B sr) := by
        dsimp only [s']; rw [hs'_eq, hfind_p, AuxTree.rotateAt_zigRight A B sr hx_ne_p.symm]
      rw [hs'_rot, hfind_p]
      exact evalMemSteps_zigRight A B sr hrev_p0 hrev_x0 hp_ht0 hx_ht0
    · have hs'_rot : s' = AuxTree.node x (AuxTree.node p_id sl C) D := by
        dsimp only [s']; rw [hs'_eq, hfind_p, AuxTree.rotateAt_zigLeft sl C D hx_ne_p.symm hsl_cond]
      rw [hs'_rot, hfind_p]
      exact evalMemSteps_zigLeft sl C D hrev_p0 hrev_x0 hp_ht0 hx_ht0
  have h5_eq0_out_sub : ∀ u ∈ t.toList, u ∉ (t.findSubtree p_id).toList → ∀ off < NODE_STRIDE,
      (g_id ≠ 0 → u = g_id → off ≠ OFF_LEFT ∧ off ≠ OFF_RIGHT) →
      nodeField st5.mem nodesBase u off = nodeField mem₀ nodesBase u off := by
    intro u hu hnin off hoff hug
    have hu_le := (ht.nodup_perm_mem hu).2
    have hup : u ≠ p_id := fun h => hnin (h ▸ hs'_perm.mem_iff.1 hp_in_s')
    have hux : u ≠ x := fun h => hnin (hs'_perm.mem_iff.1 (h ▸ hx_in_s'))
    have hnin_s' : u ∉ s'.toList := fun h => hnin (hs'_perm.mem_iff.1 h)
    rw [h5_eq4_outside_x u hu_le hux off hoff, h4_eq3_outside_p u hu_le hup off hoff]
    exact (hmem3_out u hnin_s' off hoff hug).trans (hout_mid u hu_le hnin off hoff)
  have houter_other : ∀ u ∈ t.toList, u ∉ (t.findSubtree p_id).toList →
      ∀ off < NODE_STRIDE, off ≠ OFF_LEFT → off ≠ OFF_RIGHT →
      nodeField st5.mem nodesBase u off = nodeField mem₀ nodesBase u off :=
    fun u hu hnin off hoff hL hR => h5_eq0_out_sub u hu hnin off hoff (fun _ _ => ⟨hL, hR⟩)
  have hg_left_orig : g_id ≠ 0 →
      nodeField mem₀ nodesBase g_id OFF_LEFT = mem2 (nodesBase + NODE_STRIDE * g_id + OFF_LEFT) := by
    intro hg0
    have hp_ne_root : p_id ≠ t.rootId := by
      intro h; rw [h] at hg_def
      have hne_t : t ≠ .leaf := fun hl => by simp [hl, AuxTree.toList] at hp_mem
      rw [AuxTree.parentIn_root hne_t] at hg_def; exact hg0 hg_def
    have hg_mem := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hp_ne_root).1
    rw [← hg_def] at hg_mem
    have hg_le := (ht.nodup_perm_mem hg_mem).2
    have hg_ne_x : g_id ≠ x := fun h => hg_nin_s' (h ▸ hx_in_s')
    have hg_ne_p : g_id ≠ p_id := fun h => hg_nin_s' (h ▸ hp_in_s')
    have hg_nin_sub : g_id ∉ (t.findSubtree p_id).toList := fun h => hg_nin_s' (hs'_perm.mem_iff.2 h)
    have h21 : mem2 (nodesBase + NODE_STRIDE * g_id + OFF_LEFT) =
        st_mid.mem (nodesBase + NODE_STRIDE * g_id + OFF_LEFT) := by
      dsimp only [mem2, mem1, ptrX, ptrP]
      rw [Function.update_of_ne (node_field_addr_ne hg_ne_x (by decide) (by decide)),
        Function.update_of_ne (node_field_addr_ne hg_ne_p (by decide) (by decide))]
    rw [h21]
    exact (hout_mid g_id hg_le hg_nin_sub OFF_LEFT (by decide)).symm
  have houter_lr : ∀ u ∈ t.toList, u ∉ (t.findSubtree p_id).toList →
      nodeField st5.mem nodesBase u OFF_LEFT =
        (if nodeField mem₀ nodesBase u OFF_LEFT = p_id then s'.rootId
         else nodeField mem₀ nodesBase u OFF_LEFT) ∧
      nodeField st5.mem nodesBase u OFF_RIGHT =
        (if nodeField mem₀ nodesBase u OFF_RIGHT = p_id then s'.rootId
         else nodeField mem₀ nodesBase u OFF_RIGHT) := by
    intro u hu hnin
    rcases treeMemMatch_child_field_eq_parentIn ht hnd hp_mem hu with ⟨hL_par, hR_par⟩
    by_cases hug : u = g_id ∧ g_id ≠ 0
    · rcases hug with ⟨rfl, hg0⟩
      have hu_le := (ht.nodup_perm_mem hu).2
      have hup : u ≠ p_id := fun h => hnin (h ▸ hs'_perm.mem_iff.1 hp_in_s')
      have hux : u ≠ x := fun h => hnin (hs'_perm.mem_iff.1 (h ▸ hx_in_s'))
      have hp_ne_root : p_id ≠ t.rootId := by
        intro h; rw [h] at hg_def
        have hne_t : t ≠ .leaf := fun hl => by simp [hl, AuxTree.toList] at hp_mem
        rw [AuxTree.parentIn_root hne_t] at hg_def; exact hg0 hg_def
      have hp_child := hg_def ▸ parent_child_field_of_ne_root ht hnd hp_mem hp_ne_root
      rcases hg_ne0 hg0 with ⟨gL, hgL_eq, hst3_L, hst3_R⟩
      have hgL0 : nodeField mem₀ nodesBase u OFF_LEFT = gL := (hg_left_orig hg0).trans hgL_eq.symm
      rw [h5_eq4_outside_x u hu_le hux OFF_LEFT (by decide),
          h4_eq3_outside_p u hu_le hup OFF_LEFT (by decide),
          h5_eq4_outside_x u hu_le hux OFF_RIGHT (by decide),
          h4_eq3_outside_p u hu_le hup OFF_RIGHT (by decide)]
      have h2_out : ∀ off < NODE_STRIDE, mem2 (nodesBase + NODE_STRIDE * u + off) =
          nodeField mem₀ nodesBase u off := fun off hoff => by
        dsimp only [mem2, mem1, ptrX, ptrP]
        rw [Function.update_of_ne (node_field_addr_ne hux hoff (by decide)),
            Function.update_of_ne (node_field_addr_ne hup hoff (by decide))]
        exact hout_mid u hu_le hnin off hoff
      by_cases hgl : p_id = gL
      · have hpL : nodeField mem₀ nodesBase u OFF_LEFT = p_id := hgL0.trans hgl.symm
        have hneR : nodeField mem₀ nodesBase u OFF_RIGHT ≠ p_id := (hL_par hpL).2
        simp only [hpL, ↓reduceIte, hneR, s', AuxTree.rootId]
        constructor
        · change st3.mem (nodesBase + NODE_STRIDE * u + OFF_LEFT) = x
          rw [hst3_L hgl, Function.update_self]
        · change st3.mem (nodesBase + NODE_STRIDE * u + OFF_RIGHT) = _
          rw [hst3_L hgl, Function.update_of_ne (node_same_field_addr_ne (by decide))]
          exact h2_out OFF_RIGHT (by decide)
      · have hneL : nodeField mem₀ nodesBase u OFF_LEFT ≠ p_id := fun h => hgl (hgL0 ▸ h.symm)
        have hpR : nodeField mem₀ nodesBase u OFF_RIGHT = p_id := by
          rcases hp_child with h | h <;> [exact absurd h hneL; exact h]
        simp only [hneL, ↓reduceIte, hpR, s', AuxTree.rootId]
        constructor
        · change st3.mem (nodesBase + NODE_STRIDE * u + OFF_LEFT) = _
          rw [hst3_R hgl, Function.update_of_ne (node_same_field_addr_ne (by decide))]
          exact h2_out OFF_LEFT (by decide)
        · change st3.mem (nodesBase + NODE_STRIDE * u + OFF_RIGHT) = x
          rw [hst3_R hgl, Function.update_self]
    · have hu_pos : 1 ≤ u := (ht.nodup_perm_mem hu).1
      have hneL : nodeField mem₀ nodesBase u OFF_LEFT ≠ p_id := fun h =>
        hug ⟨(hL_par h).1.trans hg_def.symm, by omega⟩
      have hneR : nodeField mem₀ nodesBase u OFF_RIGHT ≠ p_id := fun h =>
        hug ⟨(hR_par h).1.trans hg_def.symm, by omega⟩
      refine ⟨?_, ?_⟩
      · simp only [hneL, ↓reduceIte]
        exact h5_eq0_out_sub u hu hnin OFF_LEFT (by decide) (fun hg0 heq => absurd ⟨heq, hg0⟩ hug)
      · simp only [hneR, ↓reduceIte]
        exact h5_eq0_out_sub u hu hnin OFF_RIGHT (by decide) (fun hg0 heq => absurd ⟨heq, hg0⟩ hug)
  have hhp5_ge0 : mem₀ (nodesBase - 1) ≤ st5.mem (nodesBase - 1) := by
    change mem₀ (nodesBase - 1) ≤ st5_call.mem (nodesBase - 1)
    rw [← hhp3_eq]
    exact le_trans hhp4_ge hhp5_ge
  have hhp5_le0 : st5.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L := by
    change st5_call.mem (nodesBase - 1) ≤ mem₀ (nodesBase - 1) + 8 * L
    change st4_call.mem (nodesBase - 1) ≤ st3.mem (nodesBase - 1) + 4 * L at hhp4_le
    change st5_call.mem (nodesBase - 1) ≤ st4_call.mem (nodesBase - 1) + 4 * L at hhp5_le
    rw [hhp3_eq] at hhp4_le
    omega
  have hrep := AuxTree.replaceSubtree_preserves ht hnd hp_mem
    (by rw [← hg_def, ← hpp_def]; exact hx_match5)
    (by simp) hs'_perm hs'_eval5 hvcnt_5 hsteps_5
    hhp5_ge0 hag50 houter_other
    (fun u hu hnin => (houter_lr u hu hnin).1) (fun u hu hnin => (houter_lr u hu hnin).2)
  have hrot_eq : t.replaceSubtree p_id s' = t.rotateAt x := by
    calc t.replaceSubtree p_id s'
        = t.replaceSubtree p_id ((t.findSubtree p_id).rotateAt x) := by rw [← hs'_eq]
      _ = t.rotateAt x := by rw [hp_def]; exact AuxTree.replaceSubtree_rotateAt hnd hx_mem hx_ne_root
  rw [hrot_eq] at hrep
  have hout5 : ∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
      nodeField st5.mem nodesBase u off = nodeField mem₀ nodesBase u off := by
    intro u hu_le hu_nin off hoff
    have hnin_sub : u ∉ (t.findSubtree p_id).toList := fun h => hu_nin (AuxTree.findSubtree_subset h)
    have hnin_s' : u ∉ s'.toList := fun h => hnin_sub (hs'_perm.mem_iff.1 h)
    have hup : u ≠ p_id := fun h => hu_nin (h ▸ hp_mem)
    have hux : u ≠ x := fun h => hu_nin (h ▸ hx_mem)
    have hug : g_id ≠ 0 → u ≠ g_id := fun hg0 heq => by
      have hp_ne_root : p_id ≠ t.rootId := by
        intro h; rw [h] at hg_def
        have hne_t : t ≠ .leaf := fun hl => by simp [hl, AuxTree.toList] at hp_mem
        rw [AuxTree.parentIn_root hne_t] at hg_def; exact hg0 hg_def
      have hg_mem := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hp_ne_root).1
      rw [← hg_def] at hg_mem
      exact hu_nin (heq ▸ hg_mem)
    rw [h5_eq4_outside_x u hu_le hux off hoff, h4_eq3_outside_p u hu_le hup off hoff]
    exact (hmem3_out u hnin_s' off hoff (fun hg0 heq => absurd heq (hug hg0))).trans
      (hout_mid u hu_le hnin_sub off hoff)
  have hcost_le :
      5 + (5 + (c_cond + ((2 + c4 + 1) + ((2 + c5 + 1) + ((Expr.const 0).size + 1) + 1) + 1) + 1) + 1) + 1 +
        (st5.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ 2 * K_PULL L + 60 := by
    simp only [Expr.size]
    have h45 : st5_call.mem (nodesBase - 1) - mem₀ (nodesBase - 1) =
        (st5_call.mem (nodesBase - 1) - st4_call.mem (nodesBase - 1)) +
        (st4_call.mem (nodesBase - 1) - st3.mem (nodesBase - 1)) := by
      have h1 : st3.mem (nodesBase - 1) ≤ st4_call.mem (nodesBase - 1) := hhp4_ge
      have h2 : st4_call.mem (nodesBase - 1) ≤ st5_call.mem (nodesBase - 1) := hhp5_ge
      rw [← hhp3_eq]; omega
    rw [show st5.mem (nodesBase - 1) = st5_call.mem (nodesBase - 1) from rfl, h45]
    change c4 + (st4_call.mem (nodesBase - 1) - st3.mem (nodesBase - 1)) ≤ K_PULL L at hc4
    change c5 + (st5_call.mem (nodesBase - 1) - st4_call.mem (nodesBase - 1)) ≤ K_PULL L at hc5
    omega
  exact ⟨st5, _, hruns_all, hcost_le, hhp5_ge0, hhp5_le0,
    hrep.1, hrep.2.1, hrep.2.2.1, hrep.2.2.2.2, hns5, hout5, hlct05⟩

end

end MinCostFlow.LinkCut.Prog
