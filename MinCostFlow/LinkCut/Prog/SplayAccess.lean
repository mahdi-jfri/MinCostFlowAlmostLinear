module

public import MinCostFlow.LinkCut.Prog.SplayAccessDouble

/-!
Top-level splay execution theorems for L-limb `Num` path aggregates:
- `splayBody_zero_triple`: `x = 0` returns `0` immediately without modifying memory;
- `splayLoop_runs`: strong induction on depth executing `splayLoopBody` with zig / double steps;
- `splayBody_runs`: combines `pushPathBody` and `splayLoop` within `C_SPLAY_CONST L` + rank potential;
- `SplayForestOk.tree_of_mem`, `SplayForestOk.replace_tree`, and `splayForest_runs`.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM

@[expose] public section

/-- Loop body inside `splayBody`. -/
def splayLoopBody (sp : SplayProcs) : Stmt :=
  Stmt.assign 5 (nodePtrExpr 0 4) ;;
  Stmt.assign 6 (fieldLoadExpr 5 OFF_PARENT) ;;
  Stmt.cond (.reg 6)
    (Stmt.assign 7 (nodePtrExpr 0 6) ;;
     Stmt.assign 8 (fieldLoadExpr 7 OFF_LEFT) ;;
     Stmt.assign 9 (fieldLoadExpr 5 OFF_LEFT) ;;
     Stmt.assign 10 (.bin .eq (.reg 4) (.reg 8)) ;;
     Stmt.assign 11 (.bin .eq (.reg 1) (.reg 9)) ;;
     Stmt.cond (.bin .eq (.reg 10) (.reg 11))
       (Stmt.call 12 sp.rotate [.reg 0, .reg 4] ;;
        Stmt.call 12 sp.rotate [.reg 0, .reg 1])
       (Stmt.call 12 sp.rotate [.reg 0, .reg 1] ;;
        Stmt.call 12 sp.rotate [.reg 0, .reg 1]))
    (Stmt.call 12 sp.rotate [.reg 0, .reg 1]) ;;
  Stmt.assign 4 (fieldLoadExpr 3 OFF_PARENT)

private theorem frame_preserves_hdr_L {nodesBase cap : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hnb : 3 ≤ nodesBase)
    (hf : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₁ mem₂) :
    mem₂ (nodesBase - 3) = mem₁ (nodesBase - 3) := by
  refine hf.2.2.2.2.2 (nodesBase - 3) (Or.inl ⟨?_, by omega⟩)
  exact lt_of_lt_of_le (Nat.sub_lt (le_trans (by decide) hnb) (by decide)) (Nat.le_add_right _ _)

theorem AuxTree.findSubtree_rank_ge (vSize : ℕ → ℕ) {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    Nat.log 2 (1 + vSize x) ≤ (t.findSubtree x).rank vSize := by
  rcases AuxTree.findSubtree_mem_toList hx with ⟨hne, hr⟩
  cases hs : t.findSubtree x with
  | leaf => exact absurd hs hne
  | node id l r =>
      rw [hs] at hr
      simp only [AuxTree.rootId] at hr; subst hr
      simp only [AuxTree.rank]
      apply Nat.log_mono_right
      simp only [AuxTree.treeSize]
      omega

/-- When `x = 0`, `splayBody` returns `0` immediately without changing memory. -/
theorem splayBody_zero_triple {w L : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (nodesBase pos : ℕ) :
    Triple w p
      (fun st => st = startState [nodesBase, 0] mem₀ pos)
      (splayBody sp)
      (retPost fun v st' => v = 0 ∧ st'.mem = mem₀)
      (fun _ => C_SPLAY_CONST L) := by
  intro st ω hst
  subst hst
  have hr1 : (Expr.reg 1).eval w (startState [nodesBase, 0] mem₀ pos) = some 0 :=
    Expr.eval_reg_of_eq (by simp [startState])
  have hc0 : (Expr.const 0).eval w (startState [nodesBase, 0] mem₀ pos) = some 0 :=
    Expr.eval_const (Nat.pow_pos (by decide))
  refine ⟨.returned 0, startState [nodesBase, 0] mem₀ pos, 4, ?_, ⟨rfl, rfl⟩,
    by dsimp only; unfold C_SPLAY_CONST; omega⟩
  exact runs_cond_iff.mpr ⟨0, 2, hr1, runs_ret_iff.mpr ⟨0, hc0, rfl, rfl, rfl⟩, rfl⟩

private theorem splayLoop_zig_step {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    {x pp p_id : ℕ} {st : State} {t : AuxTree}
    (hL_hdr : st.mem (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1))
    (hz : ZeroFrom st.mem (st.mem (nodesBase - 1)))
    (hhp_lt : st.mem (nodesBase - 1) + 8 * L * t.depthOf x < 2 ^ w)
    (h0 : SlotZeroOk st.mem nodesBase)
    (ht : TreeMemMatch w h L st.mem nodesBase cap t 0 pp)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x,
      revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0)
    (hp_mem : p_id ∈ t.toList) (hp_par : nodeField st.mem nodesBase p_id OFF_PARENT = 0)
    (hp_eq : p_id = t.parentIn x 0)
    (hr0 : st.regs 0 = nodesBase) (hr1 : st.regs 1 = x)
    (hr3 : st.regs 3 = nodesBase + NODE_STRIDE * x) (hr4 : st.regs 4 = p_id)
    (hx12 : 1 ≤ x ∧ x ≤ cap) (hp12 : 1 ≤ p_id ∧ p_id ≤ cap) (hp_pos : p_id ≠ 0) ω :
    ∃ st' c t',
      Runs w p ω (Stmt.loop (.reg 4) (splayLoopBody sp)) st .normal st' c ∧
      st'.regs 0 = nodesBase ∧ st'.regs 1 = x ∧ st'.regs 4 = 0 ∧
      st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 8 * L * t.depthOf x ∧
      SlotZeroOk st'.mem nodesBase ∧ TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp ∧
      t'.rootId = x ∧ t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag st.mem nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps st.mem nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      revFlag st'.mem nodesBase x = false ∧ nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st.mem st'.mem ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        c + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) +
          K_SPLAY_STEP L * t'.treePhi vSize +
          3 * K_SPLAY_STEP L * (t.findSubtree x).rank vSize +
          2 * K_PUSH_PATH L * (t.depthOf x / 2) ≤
        K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * t'.rank vSize +
          (K_ROTATE L + 40) * (t.depthOf x % 2) + 2) := by
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  let ptrP := nodesBase + NODE_STRIDE * p_id
  let st5 : State := { st with regs := Function.update st.regs 5 ptrP }
  have ha5 : (nodePtrExpr 0 4).eval w st = some ptrP :=
    eval_nodePtrExpr hstride hr0 hr4 (nodePtr_lt_pow hbase hp12.2)
  have hr5_5 : st5.regs 5 = ptrP := by simp [st5]
  have ha6 : (fieldLoadExpr 5 OFF_PARENT).eval w st5 = some 0 := by
    simpa [nodeField, st5] using
      (eval_fieldLoadExpr hr5_5 (nodeAddr_lt_pow hbase hp12.2 (by decide))).trans
        (congrArg some hp_par)
  let st6 : State := { st5 with regs := Function.update st5.regs 6 0 }
  have hr6_0 : st6.regs 0 = nodesBase := by simp [st6, st5, hr0]
  have hr6_1 : st6.regs 1 = x := by simp [st6, st5, hr1]
  have hr6_3 : st6.regs 3 = nodesBase + NODE_STRIDE * x := by simp [st6, st5, hr3]
  have hr6_6 : st6.regs 6 = 0 := by simp [st6]
  have hmem60 : st6.mem = st.mem := rfl
  have hp_root : p_id = t.rootId := (ht.parent_zero_iff_root hnd hp_mem).1 hp_par
  have hp_root' : t.parentIn x 0 = t.rootId := hp_eq ▸ hp_root
  have hp_dep0 : t.depthOf p_id = 0 := (AuxTree.depthOf_zero_iff_root hp_mem).2 hp_root
  have hp_dep_info := AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hx hxr
  have hp_dep : t.depthOf p_id + 1 = t.depthOf x := by rw [hp_eq]; exact hp_dep_info.2.1
  have hx_dep1 : t.depthOf x = 1 := by omega
  have hhp_lt1 : st6.mem (nodesBase - 1) + 8 * L < 2 ^ w := by
    change st.mem (nodesBase - 1) + 8 * L < 2 ^ w
    rw [hx_dep1, Nat.mul_one] at hhp_lt; exact hhp_lt
  have hclean_zig : x ≠ t.rootId →
      (revFlag st6.mem nodesBase x = false ∧ nodeField st6.mem nodesBase x OFF_HAS_TAG = 0) ∧
      (revFlag st6.mem nodesBase (t.parentIn x 0) = false ∧
        nodeField st6.mem nodesBase (t.parentIn x 0) OFF_HAS_TAG = 0) := fun hne =>
    ⟨hclean x (AuxTree.self_mem_pathTo hx),
     hclean _ (AuxTree.mem_pathTo_parent hnd hx (AuxTree.self_mem_pathTo hx) hne)⟩
  rcases rotateBody_runs p sp st6.mem st6.pos hp_ok hbase hnb hL_hdr harena hz
      hhp_lt1 h0 ht hnd hx hclean_zig ω with
    ⟨st_rot, c_rot, hr_rot, hc_rot, hge_rot, hle_rot, ht_rot, hperm_rot, heval_rot,
     hsteps_rot, hns_rot, hout_rot, hlct_rot⟩
  rw [hmem60] at hc_rot hge_rot hle_rot heval_rot hsteps_rot hns_rot hout_rot hlct_rot
  have hnd_rot : (t.rotateAt x).toList.Nodup := hperm_rot.nodup_iff.2 hnd
  have hx_rot : x ∈ (t.rotateAt x).toList := hperm_rot.mem_iff.2 hx
  have hx_dep_after : (t.rotateAt x).depthOf x = 0 := by
    rw [AuxTree.rotateAt_depthOf_self hnd hx, hx_dep1]
  have hx_root_after : x = (t.rotateAt x).rootId :=
    (AuxTree.depthOf_zero_iff_root hx_rot).1 hx_dep_after
  have hx_par_after : nodeField st_rot.mem nodesBase x OFF_PARENT = 0 :=
    (ht_rot.parent_zero_iff_root hnd_rot hx_rot).2 hx_root_after
  let st_call : State :=
    { mem := st_rot.mem, regs := Function.update st6.regs 12 0, pos := st_rot.pos }
  have hr_call : Runs w p ω (Stmt.call 12 sp.rotate [.reg 0, .reg 1]) st6 .normal
      st_call (2 + c_rot + 1) := by
    have hargs : evalArgs w st6 [.reg 0, .reg 1] = some [nodesBase, x] := by
      simp [evalArgs, Expr.eval, hr6_0, hr6_1]
    exact runs_call_iff.mpr
      ⟨[nodesBase, x], rotateBody sp, .returned 0, st_rot, c_rot, hargs, hp_ok.rotate_eq,
       hr_rot, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hr_cond6 : Runs w p ω
      (Stmt.cond (.reg 6)
        (Stmt.assign 7 (nodePtrExpr 0 6) ;;
         Stmt.assign 8 (fieldLoadExpr 7 OFF_LEFT) ;;
         Stmt.assign 9 (fieldLoadExpr 5 OFF_LEFT) ;;
         Stmt.assign 10 (.bin .eq (.reg 4) (.reg 8)) ;;
         Stmt.assign 11 (.bin .eq (.reg 1) (.reg 9)) ;;
         Stmt.cond (.bin .eq (.reg 10) (.reg 11))
           (Stmt.call 12 sp.rotate [.reg 0, .reg 4] ;;
            Stmt.call 12 sp.rotate [.reg 0, .reg 1])
           (Stmt.call 12 sp.rotate [.reg 0, .reg 1] ;;
            Stmt.call 12 sp.rotate [.reg 0, .reg 1]))
        (Stmt.call 12 sp.rotate [.reg 0, .reg 1]))
      st6 .normal st_call (1 + (2 + c_rot + 1) + 1) :=
    runs_cond_iff.mpr ⟨0, 2 + c_rot + 1, Expr.eval_reg_of_eq hr6_6,
      by simpa using hr_call, rfl⟩
  have hr_sc3 : st_call.regs 3 = nodesBase + NODE_STRIDE * x := by simp [st_call, hr6_3]
  have ha4 : (fieldLoadExpr 3 OFF_PARENT).eval w st_call = some 0 := by
    simpa [nodeField] using
      (eval_fieldLoadExpr hr_sc3 (nodeAddr_lt_pow hbase hx12.2 (by decide))).trans
        (congrArg some hx_par_after)
  let st_end : State := { st_call with regs := Function.update st_call.regs 4 0 }
  have hr_a4 : Runs w p ω (Stmt.assign 4 (fieldLoadExpr 3 OFF_PARENT))
      st_call .normal st_end 5 :=
    runs_assign_iff.mpr ⟨0, ha4, rfl, rfl, rfl⟩
  let c_body := 6 + (5 + ((1 + (2 + c_rot + 1) + 1) + 5 + 1) + 1) + 1
  have hr_a5 : Runs w p ω (Stmt.assign 5 (nodePtrExpr 0 4)) st .normal st5 6 :=
    runs_assign_iff.mpr ⟨ptrP, ha5, rfl, rfl, rfl⟩
  have hr_a6 : Runs w p ω (Stmt.assign 6 (fieldLoadExpr 5 OFF_PARENT)) st5 .normal st6 5 :=
    runs_assign_iff.mpr ⟨0, ha6, rfl, rfl, rfl⟩
  have hr_body : Runs w p ω (splayLoopBody sp) st .normal st_end c_body :=
    runs_seq_iff.mpr (Or.inr ⟨st5, 6, _, hr_a5,
      runs_seq_iff.mpr (Or.inr ⟨st6, 5, _, hr_a6,
        runs_seq_iff.mpr (Or.inr ⟨st_call, _, 5, hr_cond6, hr_a4, rfl⟩), rfl⟩), rfl⟩)
  have hr_loop_exit : Runs w p ω (Stmt.loop (.reg 4) (splayLoopBody sp))
      st_end .normal st_end 2 :=
    runs_loop_iff.mpr (Or.inl ⟨Expr.eval_reg_of_eq (by simp [st_end]), rfl, rfl, rfl⟩)
  let c_zig := 1 + c_body + 2 + 1
  have hr_loop : Runs w p ω (Stmt.loop (.reg 4) (splayLoopBody sp))
      st .normal st_end c_zig :=
    runs_loop_iff.mpr (Or.inr (Or.inr ⟨p_id, st_end, c_body, 2,
      Expr.eval_reg_of_eq hr4, hp_pos, hr_body, hr_loop_exit, rfl⟩))
  have hmem_end : st_end.mem = st_rot.mem := rfl
  have h0_end : SlotZeroOk st_end.mem nodesBase := by
    rw [hmem_end]; exact memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct_rot
  have hclx₀ := hclean x (AuxTree.self_mem_pathTo hx)
  have hrev_x' : revFlag st_end.mem nodesBase x = false := by
    have hns' := hns_rot x hx12.2 OFF_REV (by decide)
    rw [hmem_end]; simpa [revFlag, hns'] using hclx₀.1
  have hht_x' : nodeField st_end.mem nodesBase x OFF_HAS_TAG = 0 := by
    rw [hmem_end]; exact (hns_rot x hx12.2 OFF_HAS_TAG (by decide)).trans hclx₀.2
  refine ⟨st_end, c_zig, t.rotateAt x, hr_loop, by simp [st_end, st_call, hr6_0],
    by simp [st_end, st_call, hr6_1], by simp [st_end], hge_rot,
    by rw [hmem_end, hx_dep1, Nat.mul_one]; exact hle_rot,
    h0_end, ht_rot, hx_root_after.symm, hperm_rot, heval_rot, hsteps_rot, hns_rot,
    hrev_x', hht_x', hout_rot, hlct_rot, fun vSize => ?_⟩
  have hzig := AuxTree.rotateAt_zig_phi_le vSize hnd hx hxr hp_root'
  refine ⟨AuxTree.rotateAt_treeSize vSize x t, ?_⟩
  have hphi_mul : K_SPLAY_STEP L * (t.rotateAt x).treePhi vSize +
      3 * K_SPLAY_STEP L * (t.findSubtree x).rank vSize ≤
      K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * (t.rotateAt x).rank vSize := by
    have h1 := Nat.mul_le_mul_left (K_SPLAY_STEP L) hzig.2.2
    rw [Nat.mul_add, Nat.mul_add] at h1
    have h3 : K_SPLAY_STEP L * (3 * (t.findSubtree x).rank vSize) =
        3 * K_SPLAY_STEP L * (t.findSubtree x).rank vSize := by ring
    have h3r : K_SPLAY_STEP L * (3 * (t.rotateAt x).rank vSize) =
        3 * K_SPLAY_STEP L * (t.rotateAt x).rank vSize := by ring
    omega
  rw [hmem_end, hx_dep1]
  have hmod1 : (1 : ℕ) % 2 = 1 := rfl
  have hdiv1 : (1 : ℕ) / 2 = 0 := rfl
  rw [hmod1, hdiv1, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  have hc_tot : c_zig + (st_rot.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤
      K_ROTATE L + 40 := by
    dsimp only [c_zig, c_body]; omega
  omega

private theorem splayLoop_double_step {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    {x pp p_id g_id : ℕ} {st : State} {t : AuxTree}
    (hL_hdr : st.mem (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1))
    (hz : ZeroFrom st.mem (st.mem (nodesBase - 1)))
    (hhp_lt : st.mem (nodesBase - 1) + 8 * L * t.depthOf x < 2 ^ w)
    (h0 : SlotZeroOk st.mem nodesBase)
    (ht : TreeMemMatch w h L st.mem nodesBase cap t 0 pp)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x,
      revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0)
    (hp_mem : p_id ∈ t.toList) (hp_par : nodeField st.mem nodesBase p_id OFF_PARENT = g_id)
    (hp_eq : p_id = t.parentIn x 0) (hg_eq : g_id = t.parentIn p_id 0) (hg0 : g_id ≠ 0)
    (hr0 : st.regs 0 = nodesBase) (hr1 : st.regs 1 = x)
    (hr3 : st.regs 3 = nodesBase + NODE_STRIDE * x) (hr4 : st.regs 4 = p_id)
    (hp12 : 1 ≤ p_id ∧ p_id ≤ cap) ω :
    ∃ st_next c_body t₂,
      Runs w p ω (splayLoopBody sp) st .normal st_next c_body ∧
      c_body + 2 + (st_next.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ K_DOUBLE L ∧
      st.mem (nodesBase - 1) ≤ st_next.mem (nodesBase - 1) ∧
      st_next.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L ∧
      st_next.regs 0 = nodesBase ∧ st_next.regs 1 = x ∧
      st_next.regs 3 = nodesBase + NODE_STRIDE * x ∧
      st_next.regs 4 = t₂.parentIn x 0 ∧
      st_next.mem (nodesBase - 3) = L ∧
      nodesBase + NODE_STRIDE * (cap + 1) ≤ st_next.mem (nodesBase - 1) ∧
      ZeroFrom st_next.mem (st_next.mem (nodesBase - 1)) ∧
      st_next.mem (nodesBase - 1) + 8 * L * t₂.depthOf x < 2 ^ w ∧
      SlotZeroOk st_next.mem nodesBase ∧
      TreeMemMatch w h L st_next.mem nodesBase cap t₂ 0 pp ∧
      t₂.toList.Perm t.toList ∧
      t₂.evalInorder (revFlag st_next.mem nodesBase) false =
        t.evalInorder (revFlag st.mem nodesBase) false ∧
      evalMemSteps st_next.mem nodesBase h L t₂ false 0 =
        evalMemSteps st.mem nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st_next.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      (∀ u ∈ t₂.pathTo x,
        revFlag st_next.mem nodesBase u = false ∧ nodeField st_next.mem nodesBase u OFF_HAS_TAG = 0) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st_next.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st.mem st_next.mem ∧
      2 ≤ t.depthOf x ∧ t₂.depthOf x = t.depthOf x - 2 ∧
      (∀ vSize, t₂.treeSize vSize = t.treeSize vSize ∧
        t₂.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
          t.treePhi vSize + 3 * (t₂.findSubtree x).rank vSize) := by
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  let ptrP := nodesBase + NODE_STRIDE * p_id
  let st5 : State := { st with regs := Function.update st.regs 5 ptrP }
  have ha5 : (nodePtrExpr 0 4).eval w st = some ptrP :=
    eval_nodePtrExpr hstride hr0 hr4 (nodePtr_lt_pow hbase hp12.2)
  have hr5_5 : st5.regs 5 = ptrP := by simp [st5]
  have ha6 : (fieldLoadExpr 5 OFF_PARENT).eval w st5 = some g_id := by
    simpa [nodeField, st5] using
      (eval_fieldLoadExpr hr5_5 (nodeAddr_lt_pow hbase hp12.2 (by decide))).trans
        (congrArg some hp_par)
  let st6 : State := { st5 with regs := Function.update st5.regs 6 g_id }
  have hr6_0 : st6.regs 0 = nodesBase := by simp [st6, st5, hr0]
  have hr6_1 : st6.regs 1 = x := by simp [st6, st5, hr1]
  have hr6_3 : st6.regs 3 = nodesBase + NODE_STRIDE * x := by simp [st6, st5, hr3]
  have hr6_4 : st6.regs 4 = p_id := by simp [st6, st5, hr4]
  have hr6_5 : st6.regs 5 = ptrP := by simp [st6, st5]
  have hr6_6 : st6.regs 6 = g_id := by simp [st6]
  have hmem60 : st6.mem = st.mem := rfl
  have hpr : p_id ≠ t.rootId := fun h =>
    hg0 (hg_eq.trans ((AuxTree.parentIn_eq_nodeField ht hp_mem).symm.trans
      ((ht.parent_zero_iff_root hnd hp_mem).2 h)))
  have hpr' : t.parentIn x 0 ≠ t.rootId := hp_eq ▸ hpr
  have hg_dep_info := AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hpr
  have hp_dep_info := AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hx hxr
  have hp_dep : t.depthOf p_id + 1 = t.depthOf x := hp_eq ▸ hp_dep_info.2.1
  have hdep_ge2_pre : 2 ≤ t.depthOf x := by have := hg_dep_info.2.1; omega
  have hhp_lt16 : st6.mem (nodesBase - 1) + 16 * L < 2 ^ w := by
    rw [hmem60]
    have hle16 : 16 * L ≤ 8 * L * t.depthOf x := by
      calc 16 * L = 8 * L * 2 := by ring
        _ ≤ 8 * L * t.depthOf x := Nat.mul_le_mul_left _ hdep_ge2_pre
    omega
  rcases splayDouble_exec p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt16 h0
      (st := st6) ht hnd hx hxr hpr' hclean hr6_0 hr6_1 (by rw [hp_eq] at hr6_4; exact hr6_4)
      (by simp [ptrP, hp_eq] at hr6_5; exact hr6_5) (by rw [hg_eq, hp_eq] at hr6_6; exact hr6_6) ω with
    ⟨st_dbl, c_dbl, t₂, hr_dbl, hc_dbl, hge_dbl, hle_dbl, hd0, hd1, hd3, h0_2, ht_2,
     hperm_2, heval_2, hsteps_2, hns_2, hclean_2, hout_2, hlct_2, hdep_ge2, hdep_2, hphi_2⟩
  rw [hmem60] at hc_dbl hge_dbl hle_dbl heval_2 hsteps_2 hns_2 hout_2 hlct_2
  have hr_cond6 : Runs w p ω
      (Stmt.cond (.reg 6)
        (Stmt.assign 7 (nodePtrExpr 0 6) ;;
         Stmt.assign 8 (fieldLoadExpr 7 OFF_LEFT) ;;
         Stmt.assign 9 (fieldLoadExpr 5 OFF_LEFT) ;;
         Stmt.assign 10 (.bin .eq (.reg 4) (.reg 8)) ;;
         Stmt.assign 11 (.bin .eq (.reg 1) (.reg 9)) ;;
         Stmt.cond (.bin .eq (.reg 10) (.reg 11))
           (Stmt.call 12 sp.rotate [.reg 0, .reg 4] ;;
            Stmt.call 12 sp.rotate [.reg 0, .reg 1])
           (Stmt.call 12 sp.rotate [.reg 0, .reg 1] ;;
            Stmt.call 12 sp.rotate [.reg 0, .reg 1]))
        (Stmt.call 12 sp.rotate [.reg 0, .reg 1]))
      st6 .normal st_dbl (1 + c_dbl + 1) :=
    runs_cond_iff.mpr ⟨g_id, c_dbl, Expr.eval_reg_of_eq hr6_6,
      by simpa [hg0] using hr_dbl, rfl⟩
  have hx_2 : x ∈ t₂.toList := hperm_2.mem_iff.2 hx
  have hx_2_12 := ht_2.nodup_perm_mem hx_2
  let next_p := t₂.parentIn x 0
  have hx_par2 : nodeField st_dbl.mem nodesBase x OFF_PARENT = next_p :=
    AuxTree.parentIn_eq_nodeField ht_2 hx_2
  have hd3' : st_dbl.regs 3 = nodesBase + NODE_STRIDE * x := hd3.trans hr6_3
  have ha4 : (fieldLoadExpr 3 OFF_PARENT).eval w st_dbl = some next_p := by
    simpa [nodeField, next_p] using
      (eval_fieldLoadExpr hd3' (nodeAddr_lt_pow hbase hx_2_12.2 (by decide))).trans
        (congrArg some hx_par2)
  let st_next : State := { st_dbl with regs := Function.update st_dbl.regs 4 next_p }
  have hr_a4 : Runs w p ω (Stmt.assign 4 (fieldLoadExpr 3 OFF_PARENT))
      st_dbl .normal st_next 5 :=
    runs_assign_iff.mpr ⟨next_p, ha4, rfl, rfl, rfl⟩
  let c_body := 6 + (5 + ((1 + c_dbl + 1) + 5 + 1) + 1) + 1
  have hr_a5 : Runs w p ω (Stmt.assign 5 (nodePtrExpr 0 4)) st .normal st5 6 :=
    runs_assign_iff.mpr ⟨ptrP, ha5, rfl, rfl, rfl⟩
  have hr_a6 : Runs w p ω (Stmt.assign 6 (fieldLoadExpr 5 OFF_PARENT)) st5 .normal st6 5 :=
    runs_assign_iff.mpr ⟨g_id, ha6, rfl, rfl, rfl⟩
  have hr_body : Runs w p ω (splayLoopBody sp) st .normal st_next c_body :=
    runs_seq_iff.mpr (Or.inr ⟨st5, 6, _, hr_a5,
      runs_seq_iff.mpr (Or.inr ⟨st6, 5, _, hr_a6,
        runs_seq_iff.mpr (Or.inr ⟨st_dbl, _, 5, hr_cond6, hr_a4, rfl⟩), rfl⟩), rfl⟩)
  have hmem_next : st_next.mem = st_dbl.mem := rfl
  have hmul_eq : 16 * L + 8 * L * (t.depthOf x - 2) = 8 * L * t.depthOf x := by
    have : t.depthOf x = (t.depthOf x - 2) + 2 := by omega
    conv_rhs => rw [this]
    ring
  have hhp_lt_2 : st_next.mem (nodesBase - 1) + 8 * L * t₂.depthOf x < 2 ^ w := by
    rw [hmem_next, hdep_2]
    calc st_dbl.mem (nodesBase - 1) + 8 * L * (t.depthOf x - 2)
        ≤ (st.mem (nodesBase - 1) + 16 * L) + 8 * L * (t.depthOf x - 2) := by omega
      _ = st.mem (nodesBase - 1) + (16 * L + 8 * L * (t.depthOf x - 2)) := by ring
      _ = st.mem (nodesBase - 1) + 8 * L * t.depthOf x := by rw [hmul_eq]
      _ < 2 ^ w := hhp_lt
  have hc_le : c_body + 2 + (st_next.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ K_DOUBLE L := by
    rw [hmem_next]; dsimp only [c_body]; unfold K_DOUBLE; omega
  exact ⟨st_next, c_body, t₂, hr_body, hc_le, hge_dbl, hle_dbl,
    by simp [st_next, hd0], by simp [st_next, hd1], by simp [st_next, hd3'],
    by simp [st_next, next_p],
    (frame_preserves_hdr_L hnb hlct_2).trans hL_hdr,
    le_trans harena hge_dbl, hlct_2.2.2.2.2.1, hhp_lt_2,
    h0_2, ht_2, hperm_2, heval_2, hsteps_2, hns_2, hclean_2, hout_2, hlct_2,
    hdep_ge2, hdep_2, hphi_2⟩

/-- Execution of the `splayBody` rotation loop starting with reversals and tags cleared along
`t.pathTo x`, tracking both steps and bump-heap allocation against `K_SPLAY_STEP L * ΔΦ`. -/
private lemma splay_double_arith {cb cr d1 d2 kdbl pfin p2 p0 r2 r0 rfin pp2 d200 kpp modd : ℕ}
    (h1 : cb + 2 + d1 ≤ kdbl)
    (h2 : cr + d2 + pfin + r2 + (pp2 + d200) ≤ p2 + rfin + modd + 2)
    (h3 : p2 + r0 + (kdbl + kpp + 200) ≤ p0 + r2) :
    (cr + (cb + 2)) + (d2 + d1) + pfin + r0 + ((pp2 + kpp) + (d200 + 200)) ≤
      p0 + rfin + modd + 2 := by
  omega

theorem splayLoop_credit_runs {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) :
    ∀ k x pp st t,
      t.depthOf x ≤ k →
      st.mem (nodesBase - 3) = L →
      nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1) →
      ZeroFrom st.mem (st.mem (nodesBase - 1)) →
      st.mem (nodesBase - 1) + 8 * L * t.depthOf x < 2 ^ w →
      SlotZeroOk st.mem nodesBase →
      TreeMemMatch w h L st.mem nodesBase cap t 0 pp →
      t.toList.Nodup →
      x ∈ t.toList →
      (∀ u ∈ t.pathTo x,
        revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0) →
      st.regs 0 = nodesBase →
      st.regs 1 = x →
      st.regs 3 = nodesBase + NODE_STRIDE * x →
      st.regs 4 = t.parentIn x 0 →
      ∀ ω, ∃ st' c t',
        Runs w p ω (Stmt.loop (.reg 4) (splayLoopBody sp)) st .normal st' c ∧
        st'.regs 0 = nodesBase ∧
        st'.regs 1 = x ∧
        st'.regs 4 = 0 ∧
        st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
        st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 8 * L * t.depthOf x ∧
        SlotZeroOk st'.mem nodesBase ∧
        TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp ∧
        t'.rootId = x ∧
        t'.toList.Perm t.toList ∧
        t'.evalInorder (revFlag st'.mem nodesBase) false =
          t.evalInorder (revFlag st.mem nodesBase) false ∧
        evalMemSteps st'.mem nodesBase h L t' false 0 =
          evalMemSteps st.mem nodesBase h L t false 0 ∧
        (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
          nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
        revFlag st'.mem nodesBase x = false ∧
        nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
        (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
          nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
        LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
          (nodesBase - 1) st.mem st'.mem ∧
        (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
          c + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) +
            K_SPLAY_STEP L * t'.treePhi vSize +
            3 * K_SPLAY_STEP L * (t.findSubtree x).rank vSize +
            (2 * K_PUSH_PATH L * (t.depthOf x / 2) + 200 * (t.depthOf x / 2)) ≤
          K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * t'.rank vSize +
            (K_ROTATE L + 40) * (t.depthOf x % 2) + 2) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro x pp st t hdep hL_hdr harena hz hhp_lt h0 ht hnd hx hclean hr0 hr1 hr3 hr4 ω
      have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
      have hx12 := ht.nodup_perm_mem hx
      by_cases hxr : x = t.rootId
      · have hpar0 : t.parentIn x 0 = 0 :=
          (AuxTree.parentIn_eq_nodeField ht hx).symm.trans ((ht.parent_zero_iff_root hnd hx).2 hxr)
        have hr4_0 : st.regs 4 = 0 := hr4.trans hpar0
        have hdep0 : t.depthOf x = 0 := (AuxTree.depthOf_zero_iff_root hx).2 hxr
        have hfind : t.findSubtree x = t := by
          rw [hxr]; exact AuxTree.findSubtree_root (by cases t <;> simp_all [AuxTree.toList])
        have hclx := hclean x (AuxTree.self_mem_pathTo hx)
        have hlct := lctFrame_refl (lo := nodesBase + NODE_STRIDE)
          (arenaHi := nodesBase + NODE_STRIDE * (cap + 1)) (hdrHeap := nodesBase - 1)
          (by unfold NODE_STRIDE; omega) harena hz
        refine ⟨st, 2, t,
          runs_loop_iff.mpr (Or.inl ⟨Expr.eval_reg_of_eq hr4_0, rfl, rfl, rfl⟩),
          hr0, hr1, hr4_0, le_refl _, Nat.le_add_right _ _, h0, ht, hxr.symm, List.Perm.refl _,
          rfl, rfl, fun _ _ _ _ => rfl, hclx.1, hclx.2, fun _ _ _ _ _ => rfl, hlct,
          fun vSize => ⟨rfl, ?_⟩⟩
        simp only [hdep0, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_mod, Nat.sub_self, hfind]
        omega
      · let p_id := t.parentIn x 0
        have hp_dep_info := AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hx hxr
        have hp_mem : p_id ∈ t.toList := hp_dep_info.1
        have hp12 := ht.nodup_perm_mem hp_mem
        have hp_pos : p_id ≠ 0 := by omega
        let g_id := t.parentIn p_id 0
        have hp_par_eq : nodeField st.mem nodesBase p_id OFF_PARENT = g_id :=
          AuxTree.parentIn_eq_nodeField ht hp_mem
        by_cases hg0 : g_id = 0
        · -- Zig case: `p_id = t.rootId`, so `t.depthOf x = 1`.
          have hp_root : p_id = t.rootId :=
            (ht.parent_zero_iff_root hnd hp_mem).1 (by rw [hp_par_eq, hg0])
          have hp_dep0 : t.depthOf p_id = 0 :=
            (AuxTree.depthOf_zero_iff_root hp_mem).2 hp_root
          have hdep1 : t.depthOf x = 1 := by
            have h2 := hp_dep_info.2.1
            change t.depthOf p_id + 1 = t.depthOf x at h2
            omega
          rcases splayLoop_zig_step p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 ht hnd hx hxr
              hclean hp_mem (by rw [hp_par_eq, hg0]) rfl hr0 hr1 hr3 hr4 hx12 hp12 hp_pos ω with
            ⟨st', c, t', hr, hr0', hr1', hr4', hge, hle, h0', ht', hrt', hprm', hev', hstps',
             hns', hrv', hht', hout', hlct', hphi'⟩
          refine ⟨st', c, t', hr, hr0', hr1', hr4', hge, hle, h0', ht', hrt', hprm', hev',
            hstps', hns', hrv', hht', hout', hlct', fun vSize => ?_⟩
          rcases hphi' vSize with ⟨hsz, hc_phi⟩
          refine ⟨hsz, ?_⟩
          rw [hdep1] at hc_phi ⊢
          simpa using hc_phi
        · -- Double case: `g_id ≠ 0`, so `2 ≤ t.depthOf x`.
          rcases splayLoop_double_step p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 ht hnd hx hxr
              hclean hp_mem hp_par_eq rfl rfl hg0 hr0 hr1 hr3 hr4 hp12 ω with
            ⟨st_next, c_body, t₂, hr_body, hc_iter, hge_dbl, hle_dbl, hd0, hd1, hd3', hd4,
             hL_hdr_2, harena_2, hz_2, hhp_lt_2, h0_2, ht_2, hperm_2, heval_2, hsteps_2, hns_2,
             hclean_2, hout_2, hlct_2, hdep_ge2, hdep_2, hphi_2⟩
          have hnd_2 : t₂.toList.Nodup := hperm_2.nodup_iff.2 hnd
          have hx_2 : x ∈ t₂.toList := hperm_2.mem_iff.2 hx
          have hlt_k : t₂.depthOf x < k := by omega
          rcases ih (t₂.depthOf x) hlt_k x pp st_next t₂ (Nat.le_refl _) hL_hdr_2 harena_2 hz_2
              hhp_lt_2 h0_2 ht_2 hnd_2 hx_2 hclean_2 hd0 hd1 hd3' hd4 ω with
            ⟨st_fin, c_rest, t_fin, hr_rest, hf0, hf1, hf4, hge_fin, hle_fin, h0_fin, ht_fin,
             hroot_fin, hperm_fin, heval_fin, hsteps_fin, hns_fin, hrev_fin, hht_fin, hout_fin,
             hlct_fin, hphi_fin⟩
          let c_tot := 1 + c_body + c_rest + 1
          have hr_loop : Runs w p ω (Stmt.loop (.reg 4) (splayLoopBody sp))
              st .normal st_fin c_tot :=
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨p_id, st_next, c_body, c_rest,
              Expr.eval_reg_of_eq hr4, hp_pos, hr_body, hr_rest, rfl⟩))
          have hge_tot : st.mem (nodesBase - 1) ≤ st_fin.mem (nodesBase - 1) :=
            le_trans hge_dbl hge_fin
          have hmul_eq : 16 * L + 8 * L * (t.depthOf x - 2) = 8 * L * t.depthOf x := by
            have : t.depthOf x = (t.depthOf x - 2) + 2 := by omega
            conv_rhs => rw [this]
            ring
          have hle_tot : st_fin.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 8 * L * t.depthOf x := by
            rw [hdep_2] at hle_fin
            calc st_fin.mem (nodesBase - 1)
                ≤ (st.mem (nodesBase - 1) + 16 * L) + 8 * L * (t.depthOf x - 2) := by omega
              _ = st.mem (nodesBase - 1) + (16 * L + 8 * L * (t.depthOf x - 2)) := by ring
              _ = st.mem (nodesBase - 1) + 8 * L * t.depthOf x := by rw [hmul_eq]
          refine ⟨st_fin, c_tot, t_fin, hr_loop, hf0, hf1, hf4, hge_tot, hle_tot, h0_fin, ht_fin,
            hroot_fin, hperm_fin.trans hperm_2, heval_fin.trans heval_2, hsteps_fin.trans hsteps_2,
            fun u hu off hoff => (hns_fin u hu off hoff).trans (hns_2 u hu off hoff),
            hrev_fin, hht_fin, ?_, lctFrame_trans hlct_2 hlct_fin, fun vSize => ?_⟩
          · intro u hu hnin off hoff
            have hu₂ : u ∉ t₂.toList := fun hm => hnin (hperm_2.mem_iff.1 hm)
            exact (hout_fin u hu hu₂ off hoff).trans (hout_2 u hu hnin off hoff)
          · rcases hphi_2 vSize with ⟨hsz2, hphi2⟩
            rcases hphi_fin vSize with ⟨hszf, hphif⟩
            refine ⟨hszf.trans hsz2, ?_⟩
            have hdiv : t₂.depthOf x / 2 + 1 = t.depthOf x / 2 := by omega
            have hmod : t₂.depthOf x % 2 = t.depthOf x % 2 := by omega
            have hphi2_mul : K_SPLAY_STEP L * t₂.treePhi vSize +
                3 * K_SPLAY_STEP L * (t.findSubtree x).rank vSize +
                (K_DOUBLE L + 2 * K_PUSH_PATH L + 200) ≤
                K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * (t₂.findSubtree x).rank vSize := by
              have h1 := Nat.mul_le_mul_left (K_SPLAY_STEP L) hphi2
              have hkdef : K_SPLAY_STEP L * 1 = K_DOUBLE L + 2 * K_PUSH_PATH L + 200 := by
                unfold K_SPLAY_STEP; omega
              rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, hkdef] at h1
              have h3a : K_SPLAY_STEP L * (3 * (t.findSubtree x).rank vSize) =
                  3 * K_SPLAY_STEP L * (t.findSubtree x).rank vSize := by ring
              have h3b : K_SPLAY_STEP L * (3 * (t₂.findSubtree x).rank vSize) =
                  3 * K_SPLAY_STEP L * (t₂.findSubtree x).rank vSize := by ring
              rw [h3a, h3b] at h1
              omega
            have hdiff_split : st_fin.mem (nodesBase - 1) - st.mem (nodesBase - 1) =
                (st_fin.mem (nodesBase - 1) - st_next.mem (nodesBase - 1)) +
                (st_next.mem (nodesBase - 1) - st.mem (nodesBase - 1)) := by omega
            have hc_split : c_tot = c_rest + (c_body + 2) := by dsimp only [c_tot]; omega
            have h2p : 2 * K_PUSH_PATH L * (t₂.depthOf x / 2 + 1) =
                2 * K_PUSH_PATH L * (t₂.depthOf x / 2) + 2 * K_PUSH_PATH L := by ring
            have h200 : 200 * (t₂.depthOf x / 2 + 1) = 200 * (t₂.depthOf x / 2) + 200 := by ring
            rw [← hmod, ← hdiv, h2p, h200, hdiff_split, hc_split]
            exact splay_double_arith hc_iter hphif hphi2_mul

theorem splayLoop_runs {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) :
    ∀ k x pp st t,
      t.depthOf x ≤ k →
      st.mem (nodesBase - 3) = L →
      nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1) →
      ZeroFrom st.mem (st.mem (nodesBase - 1)) →
      st.mem (nodesBase - 1) + 8 * L * t.depthOf x < 2 ^ w →
      SlotZeroOk st.mem nodesBase →
      TreeMemMatch w h L st.mem nodesBase cap t 0 pp →
      t.toList.Nodup →
      x ∈ t.toList →
      (∀ u ∈ t.pathTo x,
        revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0) →
      st.regs 0 = nodesBase →
      st.regs 1 = x →
      st.regs 3 = nodesBase + NODE_STRIDE * x →
      st.regs 4 = t.parentIn x 0 →
      ∀ ω, ∃ st' c t',
        Runs w p ω (Stmt.loop (.reg 4) (splayLoopBody sp)) st .normal st' c ∧
        st'.regs 0 = nodesBase ∧
        st'.regs 1 = x ∧
        st'.regs 4 = 0 ∧
        st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
        st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 8 * L * t.depthOf x ∧
        SlotZeroOk st'.mem nodesBase ∧
        TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp ∧
        t'.rootId = x ∧
        t'.toList.Perm t.toList ∧
        t'.evalInorder (revFlag st'.mem nodesBase) false =
          t.evalInorder (revFlag st.mem nodesBase) false ∧
        evalMemSteps st'.mem nodesBase h L t' false 0 =
          evalMemSteps st.mem nodesBase h L t false 0 ∧
        (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
          nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
        revFlag st'.mem nodesBase x = false ∧
        nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
        (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
          nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
        LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
          (nodesBase - 1) st.mem st'.mem ∧
        (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
          c + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) +
            K_SPLAY_STEP L * t'.treePhi vSize +
            3 * K_SPLAY_STEP L * (t.findSubtree x).rank vSize +
            2 * K_PUSH_PATH L * (t.depthOf x / 2) ≤
          K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * t'.rank vSize +
            (K_ROTATE L + 40) * (t.depthOf x % 2) + 2) := by
  intro k x pp st t hk hL har hz hhp h0 ht hnd hx hcl hr0 hr1 hr3 hr4 ω
  rcases splayLoop_credit_runs p sp hp_ok hbase hnb k x pp st t hk hL har hz hhp h0 ht hnd hx
      hcl hr0 hr1 hr3 hr4 ω with
    ⟨st', c, t', hr, hr0', hr1', hr4', hge, hle, h0', ht', hrt', hprm', hev', hstps', hns', hrv',
     hht', hout', hlct', hphi'⟩
  exact ⟨st', c, t', hr, hr0', hr1', hr4', hge, hle, h0', ht', hrt', hprm', hev', hstps', hns',
    hrv', hht', hout', hlct', fun vSize =>
      ⟨(hphi' vSize).1, le_trans (by omega) (hphi' vSize).2⟩⟩

/-- Full execution specification of `splayBody`: splaying `x` inside `t` brings `x` to the root,
preserves `evalInorder`, `evalMemSteps`, static payloads, and outer memory with `LctFrame`,
and satisfies the Sleator–Tarjan amortized potential bound with `C_SPLAY_CONST L`. -/
theorem splayBody_runs {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (h0 : SlotZeroOk mem₀ nodesBase)
    {t : AuxTree} {pp x : ℕ}
    (ht : TreeMemMatch w h L mem₀ nodesBase cap t 0 pp)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList)
    (hhp_lt : mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x < 2 ^ w) :
    ∀ ω, ∃ st' c t',
      Runs w p ω (splayBody sp) (startState [nodesBase, x] mem₀ pos) (.returned x) st' c ∧
      mem₀ (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤
        mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x ∧
      TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp ∧
      t'.rootId = x ∧
      t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      revFlag st'.mem nodesBase x = false ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        2 * K_PUSH_PATH L * (t.depthOf x / 2) + K_SPLAY_STEP L * t'.treePhi vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * t.rank vSize +
            (K_ROTATE L + 42) ∧
        c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) +
          K_SPLAY_STEP L * t'.treePhi vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          K_SPLAY_STEP L * t.treePhi vSize + 3 * K_SPLAY_STEP L * t.rank vSize +
            C_SPLAY_CONST L) := by
  intro ω
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  have hx12 := ht.nodup_perm_mem hx
  have hx_pos : x ≠ 0 := by omega
  rcases pushPathBody_runs p sp mem₀ pos hp_ok hbase hnb hL_hdr harena hz h0
      ht hnd hx (by omega) ω with
    ⟨st_pp, c_pp, t₁, hr_pp, hc_pp, hge_pp, ht₁, hperm₁, _hroot₁, heval₁, hsteps₁,
     hsz_pp, hdp_pp, hclean₁, hout₁, hstat₁, hlct₁⟩
  let st₀ := startState [nodesBase, x] mem₀ pos
  have hargs_pp : evalArgs w st₀ [.reg 0, .reg 1] = some [nodesBase, x] := by
    simp [evalArgs, Expr.eval, st₀, startState]
  let st₁ : State :=
    { mem := st_pp.mem, regs := Function.update st₀.regs 2 t.rootId, pos := st_pp.pos }
  have hr_call_pp : Runs w p ω (Stmt.call 2 sp.pushPath [.reg 0, .reg 1]) st₀ .normal st₁
      (2 + c_pp + 1) :=
    runs_call_iff.mpr
      ⟨[nodesBase, x], pushPathBody sp, .returned t.rootId, st_pp, c_pp, hargs_pp,
       hp_ok.pushPath_eq, hr_pp, rfl, rfl, by simp [argsSize, Expr.size]⟩
  let ptrX := nodesBase + NODE_STRIDE * x
  have hr₁_0 : st₁.regs 0 = nodesBase := by simp [st₁, st₀, startState]
  have hr₁_1 : st₁.regs 1 = x := by simp [st₁, st₀, startState]
  have ha3 : (nodePtrExpr 0 1).eval w st₁ = some ptrX :=
    eval_nodePtrExpr hstride hr₁_0 hr₁_1 (nodePtr_lt_pow hbase hx12.2)
  let st₃ : State := { st₁ with regs := Function.update st₁.regs 3 ptrX }
  have hr₃_3 : st₃.regs 3 = ptrX := by simp [st₃]
  have hnd₁ : t₁.toList.Nodup := hperm₁.nodup_iff.2 hnd
  have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.2 hx
  have hx₁_12 := ht₁.nodup_perm_mem hx₁
  let p₁ := t₁.parentIn x 0
  have hx_par₁ : nodeField st₁.mem nodesBase x OFF_PARENT = p₁ :=
    AuxTree.parentIn_eq_nodeField ht₁ hx₁
  have ha4 : (fieldLoadExpr 3 OFF_PARENT).eval w st₃ = some p₁ := by
    simpa [nodeField, st₃, p₁] using
      (eval_fieldLoadExpr hr₃_3 (nodeAddr_lt_pow hbase hx₁_12.2 (by decide))).trans
        (congrArg some hx_par₁)
  let st₄ : State := { st₃ with regs := Function.update st₃.regs 4 p₁ }
  have hL_hdr₁ : st₄.mem (nodesBase - 3) = L := (frame_preserves_hdr_L hnb hlct₁).trans hL_hdr
  have harena₁ : nodesBase + NODE_STRIDE * (cap + 1) ≤ st₄.mem (nodesBase - 1) :=
    le_trans harena hge_pp
  have hz₁ : ZeroFrom st₄.mem (st₄.mem (nodesBase - 1)) := hlct₁.2.2.2.2.1
  have h0₁ : SlotZeroOk st₄.mem nodesBase :=
    memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct₁
  have hdep_eq : t₁.depthOf x = t.depthOf x := (hdp_pp x).1
  have hhp_lt₁ : st₄.mem (nodesBase - 1) + 8 * L * t₁.depthOf x < 2 ^ w := by
    change st_pp.mem (nodesBase - 1) + 8 * L * t₁.depthOf x < 2 ^ w
    rw [hdep_eq]; omega
  rcases splayLoop_runs p sp hp_ok hbase hnb (t₁.depthOf x) x pp st₄ t₁ (Nat.le_refl _)
      hL_hdr₁ harena₁ hz₁ hhp_lt₁ h0₁ ht₁ hnd₁ hx₁ hclean₁
      (by simp [st₄, st₃, hr₁_0]) (by simp [st₄, st₃, hr₁_1])
      (by simp [st₄, hr₃_3, ptrX]) (by simp [st₄, p₁]) ω with
    ⟨st_lp, c_lp, t₂, hr_lp, _hlp0, hlp1, _hlp4, hge_lp, hle_lp, _h0_lp, ht₂, hroot₂, hperm₂,
     heval₂, hsteps₂, hns_lp, hrev_x, hht_x, hout₂, hlct₂, hphi_lp⟩
  have hret_eval : (Expr.reg 1).eval w st_lp = some x := Expr.eval_reg_of_eq hlp1
  have hr_ret : Runs w p ω (Stmt.ret (.reg 1)) st_lp (.returned x) st_lp 2 :=
    runs_ret_iff.mpr ⟨x, hret_eval, rfl, rfl, rfl⟩
  let c_all := 1 + ((2 + c_pp + 1) + (6 + (5 + (c_lp + 2 + 1) + 1) + 1) + 1) + 1
  have hr_body : Runs w p ω (splayBody sp) st₀ (.returned x) st_lp c_all := by
    refine runs_cond_iff.mpr ⟨x, _, Expr.eval_reg_of_eq (by simp [st₀, startState]), ?_, rfl⟩
    have hloop_ret := runs_seq_iff.mpr (Or.inr ⟨st_lp, c_lp, 2, hr_lp, hr_ret, rfl⟩)
    have h4_lr := runs_seq_iff.mpr
      (Or.inr ⟨st₄, 5, _, runs_assign_iff.mpr ⟨p₁, ha4, rfl, rfl, rfl⟩, hloop_ret, rfl⟩)
    have h3_4 := runs_seq_iff.mpr
      (Or.inr ⟨st₃, 6, _, runs_assign_iff.mpr ⟨ptrX, ha3, rfl, rfl, rfl⟩, h4_lr, rfl⟩)
    have h_all := runs_seq_iff.mpr (Or.inr ⟨st₁, 2 + c_pp + 1, _, hr_call_pp, h3_4, rfl⟩)
    simpa [splayBody, hx_pos, splayLoopBody] using h_all
  have hge_all : mem₀ (nodesBase - 1) ≤ st_lp.mem (nodesBase - 1) := le_trans hge_pp hge_lp
  have hle_all : st_lp.mem (nodesBase - 1) ≤
      mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x := by
    change st_lp.mem (nodesBase - 1) ≤ st_pp.mem (nodesBase - 1) + 8 * L * t₁.depthOf x at hle_lp
    rw [hdep_eq] at hle_lp; omega
  refine ⟨st_lp, c_all, t₂, hr_body, hge_all, hle_all, ht₂, hroot₂, hperm₂.trans hperm₁,
    heval₂.trans heval₁, hsteps₂.trans hsteps₁, hrev_x, hht_x, ?_, ?_,
    lctFrame_trans hlct₁ hlct₂, fun vSize => ?_⟩
  · intro u hu_le hu_nin off hoff
    have hu₁ : u ∉ t₁.toList := fun hm => hu_nin (hperm₁.mem_iff.1 hm)
    exact (hout₂ u hu_le hu₁ off hoff).trans (hout₁ u hu_le hu_nin off hoff)
  · intro u hu_le off hoff
    exact (hns_lp u hu_le off (isStaticPayloadOff_nonStruct hoff)).trans (hstat₁ u hu_le off hoff)
  · rcases hsz_pp vSize with ⟨hsz₁, hphi₁⟩
    rcases hphi_lp vSize with ⟨hsz₂, hphi₂⟩
    have hrank_out : t₂.rank vSize = t.rank vSize := by simp [AuxTree.rank, hsz₂, hsz₁]
    have hrank_x : Nat.log 2 (1 + vSize x) ≤ (t₁.findSubtree x).rank vSize :=
      AuxTree.findSubtree_rank_ge vSize hx₁
    have hrank_x_mul : 3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
        3 * K_SPLAY_STEP L * (t₁.findSubtree x).rank vSize :=
      Nat.mul_le_mul_left _ hrank_x
    have hdiv_mod : t.depthOf x = 2 * (t.depthOf x / 2) + t.depthOf x % 2 := by omega
    have hmod_le : t.depthOf x % 2 ≤ 1 := by omega
    have hc_pp_bound : c_pp + (st_pp.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤
        K_PUSH_PATH L * (2 * (t.depthOf x / 2) + t.depthOf x % 2 + 1) := by
      rw [← hdiv_mod]; exact hc_pp
    have hmul_dist : K_PUSH_PATH L * (2 * (t.depthOf x / 2) + t.depthOf x % 2 + 1) =
        2 * K_PUSH_PATH L * (t.depthOf x / 2) + K_PUSH_PATH L * (t.depthOf x % 2) + K_PUSH_PATH L := by
      ring
    rw [hmul_dist] at hc_pp_bound
    have hpp_mod : K_PUSH_PATH L * (t.depthOf x % 2) ≤ K_PUSH_PATH L :=
      (Nat.mul_le_mul_left (K_PUSH_PATH L) hmod_le).trans_eq (Nat.mul_one _)
    have hdiff_split : st_lp.mem (nodesBase - 1) - mem₀ (nodesBase - 1) =
        (st_lp.mem (nodesBase - 1) - st_pp.mem (nodesBase - 1)) +
        (st_pp.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) := by
      change st_pp.mem (nodesBase - 1) ≤ st_lp.mem (nodesBase - 1) at hge_lp; omega
    have hc_const : 2 * K_PUSH_PATH L + K_ROTATE L + 66 ≤ C_SPLAY_CONST L := by
      unfold K_PUSH_PATH K_PUSH_DOWN K_ROTATE K_PULL C_SPLAY_CONST; omega
    rw [hphi₁, hdep_eq, hrank_out] at hphi₂
    have hmem4 : st₄.mem = st_pp.mem := rfl
    rw [hmem4] at hphi₂
    have hzig_le : (K_ROTATE L + 40) * (t.depthOf x % 2) ≤ K_ROTATE L + 40 :=
      (Nat.mul_le_mul_left (K_ROTATE L + 40) hmod_le).trans_eq (Nat.mul_one _)
    have hcost_all_le : c_all + (st_lp.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) ≤
        (c_pp + (st_pp.mem (nodesBase - 1) - mem₀ (nodesBase - 1))) +
        (c_lp + (st_lp.mem (nodesBase - 1) - st_pp.mem (nodesBase - 1))) + 24 := by
      dsimp only [c_all]; rw [hdiff_split]; omega
    refine ⟨hsz₂.trans hsz₁, by omega, by omega⟩

/-- Locate the unique auxiliary tree containing `x ∈ [1, cap]` in a `SplayForestOk` forest. -/
theorem SplayForestOk.tree_of_mem {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {trees : List AuxTree} {x : ℕ}
    (hok : SplayForestOk w h L mem nodesBase cap trees) (hx1 : 1 ≤ x) (hx2 : x ≤ cap) :
    ∃ t rest, trees.Perm (t :: rest) ∧ x ∈ t.toList := by
  have hx_range : x ∈ (List.range cap).map (· + 1) :=
    List.mem_map.2 ⟨x - 1, List.mem_range.2 (by omega), by omega⟩
  have hx_flat : x ∈ trees.flatMap AuxTree.toList := hok.2.2.2.2.2.2.2.2.1.mem_iff.2 hx_range
  rcases List.mem_flatMap.1 hx_flat with ⟨t, ht, hxt⟩
  rcases exists_perm_cons_of_mem ht with ⟨rest, hperm⟩
  exact ⟨t, rest, hperm, hxt⟩

/-- Replacing one tree `t` in a `SplayForestOk` decomposition `t :: rest` by a permuted tree `t'`
preserves `SplayForestOk` when framed by `LctFrame` and non-`t` node fields are preserved. -/
theorem SplayForestOk.replace_tree {w h L : ℕ} {mem₀ mem₁ : ℕ → ℕ} {nodesBase cap : ℕ}
    {trees rest : List AuxTree} {t t' : AuxTree} {pp₁ : ℕ}
    (hok : SplayForestOk w h L mem₀ nodesBase cap trees)
    (ht_perm : trees.Perm (t :: rest))
    (hlct : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₀ mem₁)
    (hhp1_lt : mem₁ (nodesBase - 1) < 2 ^ w)
    (ht'_ne : t' ≠ .leaf)
    (ht'_perm : t'.toList.Perm t.toList)
    (ht'_m : TreeMemMatch w h L mem₁ nodesBase cap t' 0 pp₁)
    (hpp₁ : pp₁ < 2 ^ w)
    (hout : ∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
      nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off) :
    SplayForestOk w h L mem₁ nodesBase cap (t' :: rest) := by
  rcases hok with ⟨hh_pos, hwh, hnb, harena, hL_hdr, _, _, h0, hperm_all, htrees⟩
  have h0_1 : SlotZeroOk mem₁ nodesBase :=
    memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct
  have hL_1 : mem₁ (nodesBase - 3) = L := (frame_preserves_hdr_L hnb hlct).trans hL_hdr
  rcases hlct with ⟨_, _, hhp_ge, _, hz₁, hag⟩
  have hflat_perm : ((t :: rest).flatMap AuxTree.toList).Perm ((List.range cap).map (· + 1)) :=
    (list_perm_flatMap AuxTree.toList ht_perm.symm).trans hperm_all
  have hflat_nodup : ((t :: rest).flatMap AuxTree.toList).Nodup :=
    hflat_perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append] at hflat_nodup
  have hdisj := hflat_nodup.2.2
  refine ⟨hh_pos, hwh, hnb, le_trans harena hhp_ge, hL_1, hhp1_lt, hz₁, h0_1, ?_, fun s hs => ?_⟩
  · simp only [List.flatMap_cons]
    exact (ht'_perm.append_right _).trans hflat_perm
  · simp only [List.mem_cons] at hs
    rcases hs with hs_eq | hs_rest
    · rw [hs_eq]
      have hpp_eq : nodeField mem₁ nodesBase t'.rootId OFF_PPAR = pp₁ := by
        cases t' with
        | leaf => exact absurd rfl ht'_ne
        | node id l r => exact ht'_m.2.2.2.2.2.1
      exact ⟨ht'_ne, by rw [hpp_eq]; exact hpp₁, by rw [hpp_eq]; exact ht'_m⟩
    · have hs_in : s ∈ trees := ht_perm.symm.subset (by simp [hs_rest])
      rcases htrees s hs_in with ⟨hs_ne, hpp_s, hs_m⟩
      have hs_nin : ∀ u ∈ s.toList, u ∉ t.toList := fun u hus hut =>
        hdisj u hut u (List.mem_flatMap.2 ⟨s, hs_rest, hus⟩) rfl
      have hagree : ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
          nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off := fun u hus off hoff =>
        hout u (hs_m.nodup_perm_mem hus).2 (hs_nin u hus) off hoff
      have hroot_eq : nodeField mem₁ nodesBase s.rootId OFF_PPAR =
          nodeField mem₀ nodesBase s.rootId OFF_PPAR := by
        cases s with
        | leaf => exact absurd rfl hs_ne
        | node id l r => exact hagree id (by simp [AuxTree.toList]) OFF_PPAR (by decide)
      refine ⟨hs_ne, by rw [hroot_eq]; exact hpp_s, ?_⟩
      rw [hroot_eq]
      exact memAgree_treeMemMatch_of_nodeList hs_m hagree hhp_ge
        (fun a ha1 ha2 => hag a (Or.inr ⟨ha1, ha2⟩))

/-- Forest-level splay theorem maintaining `SplayForestOk` and bounding the global potential
`splayMemPhi (K_SPLAY_STEP L)`. -/
theorem splayForest_runs {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    (mem₀ : ℕ → ℕ) (pos : ℕ) {trees : List AuxTree}
    (hp_ok : SplayProgramOk w h p sp)
    (hok : SplayForestOk w h L mem₀ nodesBase cap trees)
    {t : AuxTree} {rest : List AuxTree} {x : ℕ}
    (ht_perm : trees.Perm (t :: rest)) (hx : x ∈ t.toList)
    (hhp_lt : mem₀ (nodesBase - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x < 2 ^ w) :
    ∀ ω, ∃ st' c t',
      Runs w p ω (splayBody sp) (startState [nodesBase, x] mem₀ pos) (.returned x) st' c ∧
      SplayForestOk w h L st'.mem nodesBase cap (t' :: rest) ∧
      t'.rootId = x ∧
      t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag mem₀ nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps mem₀ nodesBase h L t false 0 ∧
      revFlag st'.mem nodesBase x = false ∧
      nodeField st'.mem nodesBase x OFF_HAS_TAG = 0 ∧
      nodeField st'.mem nodesBase x OFF_PPAR = nodeField mem₀ nodesBase t.rootId OFF_PPAR ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nodesBase u off = nodeField mem₀ nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) mem₀ st'.mem ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        2 * K_PUSH_PATH L * (t.depthOf x / 2) +
          splayMemPhi (K_SPLAY_STEP L) st'.mem nodesBase cap vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          splayMemPhi (K_SPLAY_STEP L) mem₀ nodesBase cap vSize +
            3 * K_SPLAY_STEP L * t.rank vSize + (K_ROTATE L + 42) ∧
        c + (st'.mem (nodesBase - 1) - mem₀ (nodesBase - 1)) +
          splayMemPhi (K_SPLAY_STEP L) st'.mem nodesBase cap vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          splayMemPhi (K_SPLAY_STEP L) mem₀ nodesBase cap vSize +
            3 * K_SPLAY_STEP L * t.rank vSize + C_SPLAY_CONST L) := by
  intro ω
  rcases hok with ⟨hh_pos, hwh, hnb, harena, hL_hdr, hhp₀, hz, h0, hperm_all, htrees⟩
  have hok_full : SplayForestOk w h L mem₀ nodesBase cap trees :=
    ⟨hh_pos, hwh, hnb, harena, hL_hdr, hhp₀, hz, h0, hperm_all, htrees⟩
  have hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w := by omega
  have hflat_perm : ((t :: rest).flatMap AuxTree.toList).Perm ((List.range cap).map (· + 1)) :=
    (list_perm_flatMap AuxTree.toList ht_perm.symm).trans hperm_all
  have hflat_nd : ((t :: rest).flatMap AuxTree.toList).Nodup :=
    hflat_perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append] at hflat_nd
  have hnd : t.toList.Nodup := hflat_nd.1
  have ht_in : t ∈ trees := ht_perm.symm.subset (by simp)
  rcases htrees t ht_in with ⟨_ht_ne, hpp_lt, ht_m⟩
  rcases splayBody_runs p sp mem₀ pos hp_ok hbase hnb hL_hdr harena hz h0 ht_m hnd hx hhp_lt ω with
    ⟨st', c, t', hr, _hge, hle, ht'_m, hroot', hperm', heval', hsteps', hrev_x', hht_x',
     hout', hstat', hlct', hphi'⟩
  have ht'_ne : t' ≠ .leaf := by
    intro h; have := hperm'.mem_iff.2 hx; rw [h, AuxTree.toList] at this; simp at this
  have hhp1_lt : st'.mem (nodesBase - 1) < 2 ^ w := by omega
  have hok' : SplayForestOk w h L st'.mem nodesBase cap (t' :: rest) :=
    SplayForestOk.replace_tree hok_full ht_perm hlct' hhp1_lt ht'_ne hperm' ht'_m hpp_lt hout'
  have hpp_x : nodeField st'.mem nodesBase x OFF_PPAR =
      nodeField mem₀ nodesBase t.rootId OFF_PPAR := by
    rw [← hroot']
    cases t' with
    | leaf => exact absurd rfl ht'_ne
    | node id _ _ => exact ht'_m.2.2.2.2.2.1
  refine ⟨st', c, t', hr, hok', hroot', hperm', heval', hsteps', hrev_x', hht_x', hpp_x,
    hout', hstat', hlct', fun vSize => ?_⟩
  rcases hphi' vSize with ⟨hsz, hdep_phi, hphi⟩
  have hsum_eq₀ : (trees.map (AuxTree.treePhi vSize)).sum =
      t.treePhi vSize + (rest.map (AuxTree.treePhi vSize)).sum := by
    simpa [List.map_cons, List.sum_cons] using (ht_perm.map (AuxTree.treePhi vSize)).sum_eq
  have hsum_eq₁ : ((t' :: rest).map (AuxTree.treePhi vSize)).sum =
      t'.treePhi vSize + (rest.map (AuxTree.treePhi vSize)).sum := by
    simp [List.map_cons, List.sum_cons]
  rw [splayMemPhi_eq_sum hok_full, splayMemPhi_eq_sum hok', hsum_eq₀, hsum_eq₁,
      Nat.mul_add, Nat.mul_add]
  exact ⟨hsz, by omega, by omega⟩

end

end MinCostFlow.LinkCut.Prog
