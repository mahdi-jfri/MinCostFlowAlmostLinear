module

public import MinCostFlow.LinkCut.Prog.SplayStepPushDown

namespace MinCostFlow.LinkCut.Prog

/-!
`WordRAM` postcondition proofs for `pushPathBody`:
- `pushPathBody_zero_triple`: null-node early return (`x = 0`).
- `pushPathBody_runs`: recursive top-down path push using `pushDownBody_runs_in_tree`,
  clearing `OFF_REV` and `OFF_HAS_TAG` along `t.pathTo x` with `LctFrame` and
  amortized cost `K_PUSH_PATH L * (t.depthOf x + 1)`.
-/

open WordRAM

@[expose] public section

theorem AuxTree.depthOf_zero_iff_root {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    t.depthOf x = 0 ↔ x = t.rootId := by
  cases t with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r =>
      simp only [AuxTree.depthOf, AuxTree.rootId]
      by_cases heq : x = id
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        by_cases hl : x ∈ l.toList
        · simp [hl]
        · have hr : x ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h1 | rfl) | h2
            · exact absurd h1 hl
            · exact absurd rfl heq
            · exact h2
          simp [hl, hr]

theorem pushPathBody_zero_triple {w : ℕ} (p : Program) (sp : SplayProcs)
    (nodesBase : ℕ) (mem₀ : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) :
    Runs w p ω (pushPathBody sp) (startState [nodesBase, 0] mem₀ pos)
      (.returned 0) (startState [nodesBase, 0] mem₀ pos) 4 := by
  let st0 := startState [nodesBase, 0] mem₀ pos
  have hret : Runs w p ω (Stmt.ret (.const 0)) st0 (.returned 0) st0 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const (Nat.pow_pos (by decide)), rfl, rfl, rfl⟩
  exact runs_cond_iff.mpr ⟨0, 2, Expr.eval_reg_of_eq (by simp [startState]),
    by simpa [pushPathBody] using hret, by decide⟩

private theorem evalArgs_reg0_regk {w k a b : ℕ} {st : State}
    (h0 : st.regs 0 = a) (hk : st.regs k = b) :
    evalArgs w st [Expr.reg 0, Expr.reg k] = some [a, b] := by
  simp [evalArgs, Expr.eval_reg_of_eq h0, Expr.eval_reg_of_eq hk]

private theorem eval_fieldLoad_node {w nodesBase cap x off : ℕ} {st : State}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx_le : x ≤ cap) (hoff : off < NODE_STRIDE)
    (h2 : st.regs 2 = nodesBase + NODE_STRIDE * x) :
    Expr.eval w st (fieldLoadExpr 2 off) = some (nodeField st.mem nodesBase x off) :=
  eval_fieldLoadExpr h2 (nodeAddr_lt_pow hbase hx_le hoff)

private theorem nodeField_pres_of_mem_outside_subtree {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {nodesBase cap x u off : ℕ} {t : AuxTree} {parId pp : ℕ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap t parId pp)
    (hout : ∀ y ≤ cap, y ∉ (t.findSubtree x).toList → ∀ o < NODE_STRIDE,
      nodeField mem₂ nodesBase y o = nodeField mem₁ nodesBase y o)
    (_hnd : t.toList.Nodup) (hu_mem : u ∈ t.toList) (hux : u ∉ (t.findSubtree x).toList)
    (hoff : off < NODE_STRIDE) :
    nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off :=
  hout u (ht.nodup_perm_mem hu_mem).2 hux off hoff

private theorem lctFrame_preserves_hdr_L {nodesBase cap : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hnb : 3 ≤ nodesBase)
    (hf : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₁ mem₂) :
    mem₂ (nodesBase - 3) = mem₁ (nodesBase - 3) := by
  refine hf.2.2.2.2.2 (nodesBase - 3) (Or.inl ⟨?_, ?_⟩)
  · have hlt : nodesBase - 3 < nodesBase := Nat.sub_lt (le_trans (by decide) hnb) (by decide)
    exact lt_of_lt_of_le hlt (Nat.le_add_right _ _)
  · omega

private theorem pushPathBody_runs_aux : ∀ k : ℕ,
    ∀ {w h L nodesBase cap pp₀ x : ℕ} (p : Program) (sp : SplayProcs)
      (mem₀ : ℕ → ℕ) (pos : ℕ),
      SplayProgramOk w h p sp →
      nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w →
      3 ≤ nodesBase →
      mem₀ (nodesBase - 3) = L →
      nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1) →
      ZeroFrom mem₀ (mem₀ (nodesBase - 1)) →
      SlotZeroOk mem₀ nodesBase →
      ∀ {t : AuxTree},
        TreeMemMatch w h L mem₀ nodesBase cap t 0 pp₀ →
        t.toList.Nodup →
        x ∈ t.toList →
        t.depthOf x ≤ k →
        mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) < 2 ^ w →
        ∀ ω, ∃ st' c t',
          Runs w p ω (pushPathBody sp) (startState [nodesBase, x] mem₀ pos)
            (.returned t.rootId) st' c ∧
          c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤
            K_PUSH_PATH L * (t.depthOf x + 1) ∧
          mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
          TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp₀ ∧
          t'.toList.Perm t.toList ∧
          t'.rootId = t.rootId ∧
          t'.evalInorder (revFlag st'.mem nodesBase) false =
            t.evalInorder (revFlag mem₀ nodesBase) false ∧
          evalMemSteps st'.mem nodesBase h L t' false 0 =
            evalMemSteps mem₀ nodesBase h L t false 0 ∧
          (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧ t'.treePhi vSize = t.treePhi vSize) ∧
          (∀ u, t'.depthOf u = t.depthOf u ∧ t'.pathTo u = t.pathTo u) ∧
          (∀ u ∈ t'.pathTo x, revFlag st'.mem nodesBase u = false ∧
            nodeField st'.mem nodesBase u OFF_HAS_TAG = 0) ∧
          (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
            nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
          (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
            nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
          LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
            (nodesBase - 1) mem₀ st'.mem
  | 0, w, h, L, nodesBase, cap, pp₀, x, p, sp, mem₀, pos,
      hp_ok, hbase, hnb, hL_hdr, harena, hz, h0, t, ht, hnd, hx, hdep0, hhp_lt, ω => by
      have hroot : x = t.rootId := (AuxTree.depthOf_zero_iff_root hx).1 (Nat.le_zero.mp hdep0)
      subst hroot
      have hx1 : 1 ≤ t.rootId := (ht.nodup_perm_mem hx).1
      have hx_le : t.rootId ≤ cap := (ht.nodup_perm_mem hx).2
      have hx_ne0 : t.rootId ≠ 0 := Nat.ne_of_gt hx1
      have hlt_pow : nodesBase + NODE_STRIDE * t.rootId < 2 ^ w := by
        have := nodeAddr_lt_pow hbase hx_le (off := 0) (by decide)
        simpa using this
      have hstride_lt : NODE_STRIDE < 2 ^ w := by
        unfold NODE_STRIDE at hbase ⊢; omega
      let st0 := startState [nodesBase, t.rootId] mem₀ pos
      have h0_0 : st0.regs 0 = nodesBase := by simp [st0, startState]
      have h0_1 : st0.regs 1 = t.rootId := by simp [st0, startState]
      let st2 : State := { st0 with regs := Function.update st0.regs 2 (nodesBase + NODE_STRIDE * t.rootId) }
      have hr_a2 : Runs w p ω (Stmt.assign 2 (nodePtrExpr 0 1)) st0 .normal st2 6 :=
        runs_assign_iff.mpr ⟨_, eval_nodePtrExpr hstride_lt h0_0 h0_1 hlt_pow, rfl, rfl, by decide⟩
      have h2_0 : st2.regs 0 = nodesBase := by simp [st2, Function.update_of_ne, h0_0]
      have h2_1 : st2.regs 1 = t.rootId := by simp [st2, Function.update_of_ne, h0_1]
      have h2_2 : st2.regs 2 = nodesBase + NODE_STRIDE * t.rootId := by simp [st2]
      have hpar0 : nodeField st2.mem nodesBase t.rootId OFF_PARENT = 0 :=
        (ht.parent_zero_iff_root hnd hx).2 rfl
      let st3 : State := { st2 with regs := Function.update st2.regs 3 0 }
      have hr_a3 : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT)) st2 .normal st3 5 := by
        have hev := eval_fieldLoad_node (off := OFF_PARENT) hbase hx_le (by decide) h2_2
        rw [hpar0] at hev
        exact runs_assign_iff.mpr ⟨0, hev, rfl, rfl, by decide⟩
      have h3_0 : st3.regs 0 = nodesBase := by simp [st3, Function.update_of_ne, h2_0]
      have h3_1 : st3.regs 1 = t.rootId := by simp [st3, Function.update_of_ne, h2_1]
      have h3_3 : st3.regs 3 = 0 := by simp [st3]
      have hpd_hp_lt : mem₀ (nodesBase - 1) + K_PUSH_DOWN L < 2 ^ w := by
        have hle1 : 1 ≤ t.depthOf t.rootId + 1 := Nat.succ_le_succ (Nat.zero_le _)
        have hkp_le : K_PUSH_DOWN L ≤ K_PUSH_PATH L * (t.depthOf t.rootId + 1) := by
          have hk1 : K_PUSH_PATH L ≤ K_PUSH_PATH L * (t.depthOf t.rootId + 1) :=
            Nat.le_mul_of_pos_right _ hle1
          exact le_trans (by simp [K_PUSH_PATH]) hk1
        exact lt_of_le_of_lt (Nat.add_le_add_left hkp_le _) hhp_lt
      rcases pushDownBody_runs_in_tree pos hp_ok hbase hnb hL_hdr harena hz hpd_hp_lt h0 ht hnd hx ω with
        ⟨st_pd, c_pd, t', hpd_run, hpd_cost, hpd_hp, ht', ht'_perm, ht'_root, ht'_eval,
          ht'_steps, ht'_sz, ht'_dp, ht'_rev, ht'_ht, ht'_out, ht'_stat, ht'_frame⟩
      let st4 : State :=
        { mem := st_pd.mem, regs := Function.update st3.regs 5 0, pos := st_pd.pos }
      have hcall_pd : Runs w p ω (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1]) st3
          .normal st4 (2 + c_pd + 1) :=
        runs_call_iff.mpr ⟨[nodesBase, t.rootId], pushDownBody sp, .returned 0, st_pd, c_pd,
          evalArgs_reg0_regk h3_0 h3_1, hp_ok.pushDown_eq, hpd_run, rfl, rfl,
          by simp [argsSize, Expr.size]⟩
      have h4_1 : st4.regs 1 = t.rootId := by simp [st4, Function.update_of_ne, h3_1]
      have hret : Runs w p ω (Stmt.ret (.reg 1)) st4 (.returned t.rootId) st4 2 :=
        runs_ret_iff.mpr ⟨t.rootId, Expr.eval_reg_of_eq h4_1, rfl, rfl, rfl⟩
      have hinner_then : Runs w p ω
          (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 1))
          st3 (.returned t.rootId) st4 ((2 + c_pd + 1) + 2 + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st4, 2 + c_pd + 1, 2, hcall_pd, hret, rfl⟩)
      have hinner : Runs w p ω
          (Stmt.cond (.reg 3)
            (Stmt.call 4 sp.pushPath [Expr.reg 0, Expr.reg 3] ;;
              Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 4))
            (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 1)))
          st3 (.returned t.rootId) st4 (1 + ((2 + c_pd + 1) + 2 + 1) + 1) :=
        runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq h3_3, by simpa using hinner_then, rfl⟩
      have hseq32 : Runs w p ω
          (Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT) ;;
            Stmt.cond (.reg 3)
              (Stmt.call 4 sp.pushPath [Expr.reg 0, Expr.reg 3] ;;
                Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 4))
              (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 1)))
          st2 (.returned t.rootId) st4
          (5 + (1 + ((2 + c_pd + 1) + 2 + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hr_a3, hinner, rfl⟩)
      have hbody : Runs w p ω (pushPathBody sp) st0 (.returned t.rootId) st4
          (1 + (6 + (5 + (1 + ((2 + c_pd + 1) + 2 + 1) + 1) + 1) + 1) + 1) :=
        runs_cond_iff.mpr ⟨t.rootId, _, Expr.eval_reg_of_eq h0_1,
          by simpa [pushPathBody, hx_ne0] using runs_seq_iff.mpr (Or.inr ⟨st2, 6, _, hr_a2, hseq32, rfl⟩),
          rfl⟩
      have hcb : (1 + (6 + (5 + (1 + ((2 + c_pd + 1) + 2 + 1) + 1) + 1) + 1) + 1) +
          (st4.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤
          K_PUSH_PATH L * (t.depthOf t.rootId + 1) := by
        change (1 + (6 + (5 + (1 + ((2 + c_pd + 1) + 2 + 1) + 1) + 1) + 1) + 1) +
            (st_pd.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤ _
        have hle1 : 1 ≤ t.depthOf t.rootId + 1 := Nat.succ_le_succ (Nat.zero_le _)
        have hkp : K_PUSH_DOWN L + 120 ≤ K_PUSH_PATH L * (t.depthOf t.rootId + 1) :=
          Nat.le_mul_of_pos_right _ hle1
        have h1 : c_pd + (st_pd.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) + 20 ≤ K_PUSH_DOWN L + 120 := by
          omega
        exact le_trans (by omega) hkp
      have hpath_rev : ∀ u ∈ t'.pathTo t.rootId, revFlag st4.mem nodesBase u = false ∧
          nodeField st4.mem nodesBase u OFF_HAS_TAG = 0 := by
        intro u hu
        rw [(ht'_dp t.rootId).2] at hu
        have hroot_mem : t.rootId ∈ t.toList := hx
        have hp_single : t.pathTo t.rootId = [t.rootId] := by
          cases t with
          | leaf => simp [AuxTree.toList] at hroot_mem
          | node rid l r => simp [AuxTree.rootId, AuxTree.pathTo]
        rw [hp_single, List.mem_singleton] at hu
        subst hu
        exact ⟨ht'_rev, ht'_ht⟩
      have hout_t : ∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
          nodeField st4.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu hnin off hoff =>
        ht'_out u hu (fun hs => hnin (AuxTree.findSubtree_subset hs)) off hoff
      exact ⟨st4, _, t', hbody, hcb, hpd_hp, ht', ht'_perm, ht'_root, ht'_eval, ht'_steps,
        ht'_sz, ht'_dp, hpath_rev, hout_t, ht'_stat, ht'_frame⟩
  | k + 1, w, h, L, nodesBase, cap, pp₀, x, p, sp, mem₀, pos,
      hp_ok, hbase, hnb, hL_hdr, harena, hz, h0, t, ht, hnd, hx, hdep_le, hhp_lt, ω => by
      by_cases hxr : x = t.rootId
      · have hdep0 : t.depthOf x ≤ 0 := by
          subst hxr
          have := (AuxTree.depthOf_zero_iff_root hx).2 rfl
          omega
        exact pushPathBody_runs_aux 0 p sp mem₀ pos hp_ok hbase hnb hL_hdr harena hz h0
          ht hnd hx hdep0 hhp_lt ω
      · have hx1 : 1 ≤ x := (ht.nodup_perm_mem hx).1
        have hx_le : x ≤ cap := (ht.nodup_perm_mem hx).2
        have hx_ne0 : x ≠ 0 := Nat.ne_of_gt hx1
        have hlt_pow : nodesBase + NODE_STRIDE * x < 2 ^ w := by
          have := nodeAddr_lt_pow hbase hx_le (off := 0) (by decide)
          simpa using this
        have hstride_lt : NODE_STRIDE < 2 ^ w := by
          unfold NODE_STRIDE at hbase ⊢; omega
        let st0 := startState [nodesBase, x] mem₀ pos
        have h0_0 : st0.regs 0 = nodesBase := by simp [st0, startState]
        have h0_1 : st0.regs 1 = x := by simp [st0, startState]
        let st2 : State := { st0 with regs := Function.update st0.regs 2 (nodesBase + NODE_STRIDE * x) }
        have hr_a2 : Runs w p ω (Stmt.assign 2 (nodePtrExpr 0 1)) st0 .normal st2 6 :=
          runs_assign_iff.mpr ⟨_, eval_nodePtrExpr hstride_lt h0_0 h0_1 hlt_pow, rfl, rfl, by decide⟩
        have h2_0 : st2.regs 0 = nodesBase := by simp [st2, Function.update_of_ne, h0_0]
        have h2_1 : st2.regs 1 = x := by simp [st2, Function.update_of_ne, h0_1]
        have h2_2 : st2.regs 2 = nodesBase + NODE_STRIDE * x := by simp [st2]
        let px := t.parentIn x 0
        have hpar_eq : nodeField st2.mem nodesBase x OFF_PARENT = px :=
          AuxTree.parentIn_eq_nodeField ht hx
        rcases AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hx hxr with
          ⟨hpx_mem, hpx_dep, hpath_split⟩
        change px ∈ t.toList at hpx_mem
        change t.depthOf px + 1 = t.depthOf x at hpx_dep
        change t.pathTo x = t.pathTo px ++ [x] at hpath_split
        have hpx_pos : 1 ≤ px := ht.parent_pos_of_ne_root hnd hx hxr
        have hpx_ne0 : px ≠ 0 := Nat.ne_of_gt hpx_pos
        let st3 : State := { st2 with regs := Function.update st2.regs 3 px }
        have hr_a3 : Runs w p ω (Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT)) st2 .normal st3 5 := by
          have hev := eval_fieldLoad_node (off := OFF_PARENT) hbase hx_le (by decide) h2_2
          rw [hpar_eq] at hev
          exact runs_assign_iff.mpr ⟨px, hev, rfl, rfl, by decide⟩
        have h3_0 : st3.regs 0 = nodesBase := by simp [st3, Function.update_of_ne, h2_0]
        have h3_1 : st3.regs 1 = x := by simp [st3, Function.update_of_ne, h2_1]
        have h3_3 : st3.regs 3 = px := by simp [st3]
        have hpx_dep_k : t.depthOf px ≤ k := by omega
        have hhp_lt_px : mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf px + 1) < 2 ^ w := by
          have hle_m : K_PUSH_PATH L * (t.depthOf px + 1) ≤ K_PUSH_PATH L * (t.depthOf x + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          exact lt_of_le_of_lt (Nat.add_le_add_left hle_m _) hhp_lt
        rcases pushPathBody_runs_aux k p sp mem₀ pos hp_ok hbase hnb hL_hdr harena hz h0
            ht hnd hpx_mem hpx_dep_k hhp_lt_px ω with
          ⟨st1, c1, t1, hr1, hc1, hhp1, ht1, ht1_perm, ht1_root, ht1_eval, ht1_steps,
            ht1_sz, ht1_dp, ht1_path, ht1_out, ht1_stat, hlct01⟩
        let st4 : State :=
          { mem := st1.mem, regs := Function.update st3.regs 4 t.rootId, pos := st1.pos }
        have hcall_pp : Runs w p ω (Stmt.call 4 sp.pushPath [Expr.reg 0, Expr.reg 3]) st3
            .normal st4 (2 + c1 + 1) :=
          runs_call_iff.mpr ⟨[nodesBase, px], pushPathBody sp, .returned t.rootId, st1, c1,
            evalArgs_reg0_regk h3_0 h3_3, hp_ok.pushPath_eq, hr1, rfl, rfl,
            by simp [argsSize, Expr.size]⟩
        have h4_0 : st4.regs 0 = nodesBase := by simp [st4, Function.update_of_ne, h3_0]
        have h4_1 : st4.regs 1 = x := by simp [st4, Function.update_of_ne, h3_1]
        have h4_4 : st4.regs 4 = t.rootId := by simp [st4]
        have hL_hdr1 : st1.mem (nodesBase - 3) = L :=
          (lctFrame_preserves_hdr_L hnb hlct01).trans hL_hdr
        have harena1 : nodesBase + NODE_STRIDE * (cap + 1) ≤ st1.mem (nodesBase - 1) :=
          le_trans harena hhp1
        have hz1 : ZeroFrom st1.mem (st1.mem (nodesBase - 1)) := hlct01.2.2.2.2.1
        have h01 : SlotZeroOk st1.mem nodesBase :=
          memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct01
        have hnd1 : t1.toList.Nodup := ht1_perm.nodup_iff.mpr hnd
        have hx1_mem : x ∈ t1.toList := ht1_perm.mem_iff.mpr hx
        have hpd_hp_lt1 : st1.mem (nodesBase - 1) + K_PUSH_DOWN L < 2 ^ w := by
          have hle_diff : st1.mem (nodesBase - 1) - mem₀ (nodesBase - 1) ≤
              K_PUSH_PATH L * (t.depthOf px + 1) := le_trans (Nat.le_add_left _ c1) hc1
          have hst1_le : st1.mem (nodesBase - 1) ≤
              mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf px + 1) := by omega
          have hsum_le : st1.mem (nodesBase - 1) + K_PUSH_DOWN L ≤
              mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) := by
            have hkp_mul : K_PUSH_PATH L * (t.depthOf px + 1) + K_PUSH_PATH L =
                K_PUSH_PATH L * (t.depthOf x + 1) := by
              rw [← hpx_dep]; ring
            have hkd_le : K_PUSH_DOWN L ≤ K_PUSH_PATH L := by simp [K_PUSH_PATH]
            omega
          exact lt_of_le_of_lt hsum_le hhp_lt
        rcases pushDownBody_runs_in_tree st1.pos hp_ok hbase hnb hL_hdr1 harena1 hz1 hpd_hp_lt1 h01
            ht1 hnd1 hx1_mem ω with
          ⟨st2', c2, t2, hpd_run, hc2, hhp2, ht2, ht2_perm, ht2_root, ht2_eval, ht2_steps,
            ht2_sz, ht2_dp, ht2_rev, ht2_ht, ht2_out, ht2_stat, hlct12⟩
        let st5 : State :=
          { mem := st2'.mem, regs := Function.update st4.regs 5 0, pos := st2'.pos }
        have hcall_pd : Runs w p ω (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1]) st4
            .normal st5 (2 + c2 + 1) :=
          runs_call_iff.mpr ⟨[nodesBase, x], pushDownBody sp, .returned 0, st2', c2,
            evalArgs_reg0_regk h4_0 h4_1, hp_ok.pushDown_eq, hpd_run, rfl, rfl,
            by simp [argsSize, Expr.size]⟩
        have h5_4 : st5.regs 4 = t.rootId := by simp [st5, Function.update_of_ne, h4_4]
        have hret : Runs w p ω (Stmt.ret (.reg 4)) st5 (.returned t.rootId) st5 2 :=
          runs_ret_iff.mpr ⟨t.rootId, Expr.eval_reg_of_eq h5_4, rfl, rfl, rfl⟩
        have hthen_tail : Runs w p ω
            (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 4))
            st4 (.returned t.rootId) st5 ((2 + c2 + 1) + 2 + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st5, 2 + c2 + 1, 2, hcall_pd, hret, rfl⟩)
        have hthen : Runs w p ω
            (Stmt.call 4 sp.pushPath [Expr.reg 0, Expr.reg 3] ;;
              Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 4))
            st3 (.returned t.rootId) st5 ((2 + c1 + 1) + ((2 + c2 + 1) + 2 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st4, 2 + c1 + 1, _, hcall_pp, hthen_tail, rfl⟩)
        have hinner : Runs w p ω
            (Stmt.cond (.reg 3)
              (Stmt.call 4 sp.pushPath [Expr.reg 0, Expr.reg 3] ;;
                Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 4))
              (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 1)))
            st3 (.returned t.rootId) st5 (1 + ((2 + c1 + 1) + ((2 + c2 + 1) + 2 + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨px, _, Expr.eval_reg_of_eq h3_3, by simpa [hpx_ne0] using hthen, rfl⟩
        have hseq32 : Runs w p ω
            (Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT) ;;
              Stmt.cond (.reg 3)
                (Stmt.call 4 sp.pushPath [Expr.reg 0, Expr.reg 3] ;;
                  Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 4))
                (Stmt.call 5 sp.pushDown [Expr.reg 0, Expr.reg 1] ;; Stmt.ret (.reg 1)))
            st2 (.returned t.rootId) st5
            (5 + (1 + ((2 + c1 + 1) + ((2 + c2 + 1) + 2 + 1) + 1) + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hr_a3, hinner, rfl⟩)
        have hbody : Runs w p ω (pushPathBody sp) st0 (.returned t.rootId) st5
            (1 + (6 + (5 + (1 + ((2 + c1 + 1) + ((2 + c2 + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨x, _, Expr.eval_reg_of_eq h0_1,
            by simpa [pushPathBody, hx_ne0] using runs_seq_iff.mpr (Or.inr ⟨st2, 6, _, hr_a2, hseq32, rfl⟩),
            rfl⟩
        have hcb : (1 + (6 + (5 + (1 + ((2 + c1 + 1) + ((2 + c2 + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) +
            (st5.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤
            K_PUSH_PATH L * (t.depthOf x + 1) := by
          have hdiff : st5.mem (nodesBase - 1) - mem₀ (nodesBase - 1) =
              (st1.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) +
              (st2'.mem (nodesBase - 1) - st1.mem (nodesBase - 1)) := by
            change st2'.mem (nodesBase - 1) - mem₀ (nodesBase - 1) = _
            omega
          have hkp_mul : K_PUSH_PATH L * (t.depthOf px + 1) + K_PUSH_PATH L =
              K_PUSH_PATH L * (t.depthOf x + 1) := by
            rw [← hpx_dep]; ring
          have hkp_def : K_PUSH_DOWN L + 120 = K_PUSH_PATH L := rfl
          calc
            (1 + (6 + (5 + (1 + ((2 + c1 + 1) + ((2 + c2 + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) +
                (st5.mem (nodesBase - 1) - mem₀ (nodesBase - 1))
              = (c1 + (st1.mem (nodesBase - 1) - mem₀ (nodesBase - 1))) +
                  (c2 + (st2'.mem (nodesBase - 1) - st1.mem (nodesBase - 1))) + 27 := by
                rw [hdiff]; omega
            _ ≤ K_PUSH_PATH L * (t.depthOf px + 1) + K_PUSH_DOWN L + 27 := by
                gcongr
            _ ≤ K_PUSH_PATH L * (t.depthOf px + 1) + K_PUSH_PATH L := by
                rw [← hkp_def]; omega
            _ = K_PUSH_PATH L * (t.depthOf x + 1) := hkp_mul
        have hpath_rev : ∀ u ∈ t2.pathTo x, revFlag st5.mem nodesBase u = false ∧
            nodeField st5.mem nodesBase u OFF_HAS_TAG = 0 := by
          intro u hu
          rw [(ht2_dp x).2, (ht1_dp x).2, hpath_split, List.mem_append, List.mem_singleton] at hu
          rcases hu with hu_px | rfl
          · have hu_px1 : u ∈ t1.pathTo px := by rwa [(ht1_dp px).2]
            have hu_mem1 : u ∈ t1.toList := AuxTree.mem_pathTo hu_px1
            have hpx_mem1 : px ∈ t1.toList := ht1_perm.mem_iff.mpr hpx_mem
            have hdep_lt : t1.depthOf px < t1.depthOf x := by
              rw [(ht1_dp px).1, (ht1_dp x).1]; omega
            have hu_not_sub : u ∉ (t1.findSubtree x).toList :=
              AuxTree.not_mem_findSubtree_of_ancestor hnd1 hpx_mem1 hx1_mem hdep_lt hu_px1
            have hrev_u : nodeField st5.mem nodesBase u OFF_REV =
                nodeField st1.mem nodesBase u OFF_REV :=
              nodeField_pres_of_mem_outside_subtree ht1 ht2_out hnd1 hu_mem1 hu_not_sub (by decide)
            have hht_u : nodeField st5.mem nodesBase u OFF_HAS_TAG =
                nodeField st1.mem nodesBase u OFF_HAS_TAG :=
              nodeField_pres_of_mem_outside_subtree ht1 ht2_out hnd1 hu_mem1 hu_not_sub (by decide)
            have ⟨h1, h2⟩ := ht1_path u hu_px1
            exact ⟨by simpa [revFlag, hrev_u] using h1, by rw [hht_u]; exact h2⟩
          · exact ⟨ht2_rev, ht2_ht⟩
        have hout_t : ∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
            nodeField st5.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu hnin off hoff => by
          have hnin1 : u ∉ (t1.findSubtree x).toList := fun hs =>
            hnin (ht1_perm.mem_iff.mp (AuxTree.findSubtree_subset hs))
          exact (ht2_out u hu hnin1 off hoff).trans (ht1_out u hu hnin off hoff)
        have hstat_t : ∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
            nodeField st5.mem nodesBase u off = nodeField mem₀ nodesBase u off := fun u hu off hoff =>
          (ht2_stat u hu off hoff).trans (ht1_stat u hu off hoff)
        exact ⟨st5, _, t2, hbody, hcb, le_trans hhp1 hhp2, ht2, ht2_perm.trans ht1_perm,
          ht2_root.trans ht1_root, ht2_eval.trans ht1_eval, ht2_steps.trans ht1_steps,
          fun vSize => ⟨(ht2_sz vSize).1.trans (ht1_sz vSize).1, (ht2_sz vSize).2.trans (ht1_sz vSize).2⟩,
          fun u => ⟨(ht2_dp u).1.trans (ht1_dp u).1, (ht2_dp u).2.trans (ht1_dp u).2⟩,
          hpath_rev, hout_t, hstat_t, lctFrame_trans hlct01 hlct12⟩

theorem pushPathBody_runs {w h L nodesBase cap pp₀ x : ℕ}
    (p : Program) (sp : SplayProcs) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree}
    (ht : TreeMemMatch w h L mem₀ nodesBase cap t 0 pp₀)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList)
    (hhp_lt : mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) < 2 ^ w)
    (ω : ℕ → Bool) :
    ∃ st' c t',
      Runs w p ω (pushPathBody sp) (startState [nodesBase, x] mem₀ pos)
        (.returned t.rootId) st' c ∧
      c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤
        K_PUSH_PATH L * (t.depthOf x + 1) ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp₀ ∧
      t'.toList.Perm t.toList ∧
      t'.rootId = t.rootId ∧
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧ t'.treePhi vSize = t.treePhi vSize) ∧
      (∀ u, t'.depthOf u = t.depthOf u ∧ t'.pathTo u = t.pathTo u) ∧
      (∀ u ∈ t'.pathTo x, revFlag st'.mem nodesBase u = false ∧
        nodeField st'.mem nodesBase u OFF_HAS_TAG = 0) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem :=
  pushPathBody_runs_aux (t.depthOf x) p sp mem₀ pos hp_ok hbase hnb hL_hdr harena hz h0
    ht hnd hx le_rfl hhp_lt ω

end

end MinCostFlow.LinkCut.Prog
