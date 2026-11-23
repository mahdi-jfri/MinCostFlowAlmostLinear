module

public import MinCostFlow.LinkCut.Prog.SplayAccessPure

/-!
Double-rotation execution lemmas for `splayBody`:
- `double_zigZig_exec`: executes `[nodesBase, p_id]` followed by `[nodesBase, x]`;
- `double_zigZag_exec`: executes `[nodesBase, x]` twice;
- `splayDouble_exec`: selects zig-zig vs zig-zag via left-child comparisons, preserving
  `TreeMemMatch`, `evalInorder`, `evalMemSteps`, `LctFrame`, and the Sleator–Tarjan
  double-step potential drop within `2 * K_ROTATE L + 50` steps+heap and `16 * L` heap growth.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM

@[expose] public section

private theorem frame_preserves_hdr_L {nodesBase cap : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hnb : 3 ≤ nodesBase)
    (hf : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₁ mem₂) :
    mem₂ (nodesBase - 3) = mem₁ (nodesBase - 3) := by
  refine hf.2.2.2.2.2 (nodesBase - 3) (Or.inl ⟨?_, by omega⟩)
  exact lt_of_lt_of_le (Nat.sub_lt (le_trans (by decide) hnb) (by decide)) (Nat.le_add_right _ _)

private theorem tmm_children {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap x par pp : ℕ} {l r : AuxTree}
    (ht : TreeMemMatch w h L mem nodesBase cap (.node x l r) par pp) :
    nodeField mem nodesBase x OFF_LEFT = l.rootId ∧
    nodeField mem nodesBase x OFF_RIGHT = r.rootId ∧
    TreeMemMatch w h L mem nodesBase cap l x 0 ∧
    TreeMemMatch w h L mem nodesBase cap r x 0 := by
  rcases ht with ⟨_, _, hL, hR, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
  exact ⟨hL, hR, hl, hr⟩

private theorem clean_of_nonStruct_subpath {cap : ℕ} {nodesBase : ℕ} {m₁ m₂ : ℕ → ℕ}
    {t t' : AuxTree} {x : ℕ}
    (hns : ∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
      nodeField m₂ nodesBase u off = nodeField m₁ nodesBase u off)
    (hm_t : ∀ u ∈ t.toList, u ≤ cap)
    (hsub : ∀ u ∈ t'.pathTo x, u ∈ t.pathTo x)
    (hclean : ∀ u ∈ t.pathTo x,
      revFlag m₁ nodesBase u = false ∧ nodeField m₁ nodesBase u OFF_HAS_TAG = 0) :
    ∀ u ∈ t'.pathTo x,
      revFlag m₂ nodesBase u = false ∧ nodeField m₂ nodesBase u OFF_HAS_TAG = 0 := by
  intro u hu
  have hu_t := AuxTree.mem_pathTo (hsub u hu)
  have hu_le := hm_t u hu_t
  have hclean_u := hclean u (hsub u hu)
  have hrev_u : revFlag m₂ nodesBase u = revFlag m₁ nodesBase u := by
    simp [revFlag, hns u hu_le OFF_REV (by decide)]
  exact ⟨hrev_u.trans hclean_u.1, (hns u hu_le OFF_HAS_TAG (by decide)).trans hclean_u.2⟩

private theorem double_pair_exec {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    {st : State} (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase)
    (hL_hdr : st.mem (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1))
    (hz : ZeroFrom st.mem (st.mem (nodesBase - 1)))
    (hhp_lt : st.mem (nodesBase - 1) + 16 * L < 2 ^ w)
    (h0 : SlotZeroOk st.mem nodesBase)
    {t : AuxTree} {pp x a rFirst : ℕ}
    (ht : TreeMemMatch w h L st.mem nodesBase cap t 0 pp) (hnd : t.toList.Nodup)
    (hx : x ∈ t.toList) (ha : a ∈ t.toList) (ha_path : a ∈ t.pathTo x)
    (hclean : ∀ u ∈ t.pathTo x,
      revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0)
    (hrFirst : rFirst < 12)
    (hr0 : st.regs 0 = nodesBase) (hr1 : st.regs 1 = x) (hra : st.regs rFirst = a)
    (ω : ℕ → Bool) :
    ∃ st' c,
      Runs w p ω
        (Stmt.call 12 sp.rotate [.reg 0, .reg rFirst] ;;
         Stmt.call 12 sp.rotate [.reg 0, .reg 1]) st .normal st' c ∧
      c + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ 2 * K_ROTATE L + 10 ∧
      st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L ∧
      (∀ r < 12, st'.regs r = st.regs r) ∧
      SlotZeroOk st'.mem nodesBase ∧
      TreeMemMatch w h L st'.mem nodesBase cap ((t.rotateAt a).rotateAt x) 0 pp ∧
      ((t.rotateAt a).rotateAt x).toList.Perm t.toList ∧
      ((t.rotateAt a).rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag st.mem nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L ((t.rotateAt a).rotateAt x) false 0 =
        evalMemSteps st.mem nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      (∀ u ∈ ((t.rotateAt a).rotateAt x).pathTo x,
        revFlag st'.mem nodesBase u = false ∧ nodeField st'.mem nodesBase u OFF_HAS_TAG = 0) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st.mem st'.mem := by
  have hclean₁ : a ≠ t.rootId →
      (revFlag st.mem nodesBase a = false ∧ nodeField st.mem nodesBase a OFF_HAS_TAG = 0) ∧
      (revFlag st.mem nodesBase (t.parentIn a 0) = false ∧
        nodeField st.mem nodesBase (t.parentIn a 0) OFF_HAS_TAG = 0) := fun hne =>
    ⟨hclean a ha_path, hclean _ (AuxTree.mem_pathTo_parent hnd hx ha_path hne)⟩
  rcases rotateBody_runs p sp st.mem st.pos hp_ok hbase hnb hL_hdr harena hz (by omega) h0
      ht hnd ha hclean₁ ω with
    ⟨st₁_call, c₁, hr₁, hc₁, hge₁, hle₁, ht₁, hperm₁, heval₁, hsteps₁, hns₁, hout₁, hlct₁⟩
  let st₁ : State := { st₁_call with regs := Function.update st.regs 12 0 }
  have hcall₁ : Runs w p ω (Stmt.call 12 sp.rotate [.reg 0, .reg rFirst]) st .normal st₁
      (2 + c₁ + 1) := by
    have hargs : evalArgs w st [.reg 0, .reg rFirst] = some [nodesBase, a] := by
      simp [evalArgs, Expr.eval, hr0, hra]
    exact runs_call_iff.mpr ⟨[nodesBase, a], rotateBody sp, .returned 0, st₁_call, c₁,
      hargs, hp_ok.rotate_eq, hr₁, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hL_hdr₁ : st₁.mem (nodesBase - 3) = L := (frame_preserves_hdr_L hnb hlct₁).trans hL_hdr
  have harena₁ : nodesBase + NODE_STRIDE * (cap + 1) ≤ st₁.mem (nodesBase - 1) :=
    le_trans harena hge₁
  have hz₁ : ZeroFrom st₁.mem (st₁.mem (nodesBase - 1)) := hlct₁.2.2.2.2.1
  have h0₁ : SlotZeroOk st₁.mem nodesBase :=
    memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct₁
  have hhp_lt₁ : st₁.mem (nodesBase - 1) + 8 * L < 2 ^ w := by
    change st₁_call.mem (nodesBase - 1) + 8 * L < 2 ^ w; omega
  have hnd₁ : (t.rotateAt a).toList.Nodup := hperm₁.nodup_iff.2 hnd
  have hx₁ : x ∈ (t.rotateAt a).toList := hperm₁.mem_iff.2 hx
  have hpath₁ : ∀ u ∈ (t.rotateAt a).pathTo x, u ∈ t.pathTo x :=
    AuxTree.rotateAt_pathTo_subset hnd hx ha_path
  have hclean_path₁ : ∀ u ∈ (t.rotateAt a).pathTo x,
      revFlag st₁.mem nodesBase u = false ∧ nodeField st₁.mem nodesBase u OFF_HAS_TAG = 0 :=
    clean_of_nonStruct_subpath hns₁ (fun _ hu => (ht.nodup_perm_mem hu).2) hpath₁ hclean
  have hclean₂ : x ≠ (t.rotateAt a).rootId →
      (revFlag st₁.mem nodesBase x = false ∧ nodeField st₁.mem nodesBase x OFF_HAS_TAG = 0) ∧
      (revFlag st₁.mem nodesBase ((t.rotateAt a).parentIn x 0) = false ∧
        nodeField st₁.mem nodesBase ((t.rotateAt a).parentIn x 0) OFF_HAS_TAG = 0) := fun hne =>
    ⟨hclean_path₁ x (AuxTree.self_mem_pathTo hx₁),
     hclean_path₁ _ (AuxTree.mem_pathTo_parent hnd₁ hx₁ (AuxTree.self_mem_pathTo hx₁) hne)⟩
  rcases rotateBody_runs p sp st₁.mem st₁.pos hp_ok hbase hnb hL_hdr₁ harena₁ hz₁ hhp_lt₁ h0₁
      ht₁ hnd₁ hx₁ hclean₂ ω with
    ⟨st₂_call, c₂, hr₂, hc₂, hge₂, hle₂, ht₂, hperm₂, heval₂, hsteps₂, hns₂, hout₂, hlct₂⟩
  let st₂ : State := { st₂_call with regs := Function.update st₁.regs 12 0 }
  have hcall₂ : Runs w p ω (Stmt.call 12 sp.rotate [.reg 0, .reg 1]) st₁ .normal st₂
      (2 + c₂ + 1) := by
    have hargs : evalArgs w st₁ [.reg 0, .reg 1] = some [nodesBase, x] := by
      have h10 : st₁.regs 0 = nodesBase := by simp [st₁, hr0]
      have h11 : st₁.regs 1 = x := by simp [st₁, hr1]
      simp [evalArgs, Expr.eval, h10, h11]
    exact runs_call_iff.mpr ⟨[nodesBase, x], rotateBody sp, .returned 0, st₂_call, c₂,
      hargs, hp_ok.rotate_eq, hr₂, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hnd₂ : ((t.rotateAt a).rotateAt x).toList.Nodup := hperm₂.nodup_iff.2 hnd₁
  have hx₂ : x ∈ ((t.rotateAt a).rotateAt x).toList := hperm₂.mem_iff.2 hx₁
  have hpath₂ : ∀ u ∈ ((t.rotateAt a).rotateAt x).pathTo x, u ∈ (t.rotateAt a).pathTo x :=
    AuxTree.rotateAt_pathTo_subset hnd₁ hx₁ (AuxTree.self_mem_pathTo hx₁)
  have hclean_path₂ :=
    clean_of_nonStruct_subpath hns₂ (fun _ hu => (ht₁.nodup_perm_mem hu).2) hpath₂ hclean_path₁
  have hlct₀₂ : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) st.mem st₂.mem := lctFrame_trans hlct₁ hlct₂
  have _ := (⟨hrFirst, hnd₂, hx₂⟩ : rFirst < 12 ∧ _ ∧ _)
  refine ⟨st₂, (2 + c₁ + 1) + (2 + c₂ + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨st₁, _, _, hcall₁, hcall₂, rfl⟩), ?_, ?_, ?_, ?_, ?_, ht₂,
    hperm₂.trans hperm₁, heval₂.trans heval₁, hsteps₂.trans hsteps₁,
    fun u hu off hoff => (hns₂ u hu off hoff).trans (hns₁ u hu off hoff), hclean_path₂,
    fun u hu hnin off hoff =>
      (hout₂ u hu (fun hm => hnin (hperm₁.mem_iff.1 hm)) off hoff).trans (hout₁ u hu hnin off hoff),
    hlct₀₂⟩
  · change _ + (st₂_call.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ _
    change st.mem (nodesBase - 1) ≤ st₁_call.mem (nodesBase - 1) at hge₁
    change st₁_call.mem (nodesBase - 1) ≤ st₂_call.mem (nodesBase - 1) at hge₂
    change c₂ + (st₂_call.mem (nodesBase - 1) - st₁_call.mem (nodesBase - 1)) ≤ K_ROTATE L at hc₂
    omega
  · change st.mem (nodesBase - 1) ≤ st₂_call.mem (nodesBase - 1); exact le_trans hge₁ hge₂
  · change st₂_call.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L
    change st₁_call.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 8 * L at hle₁
    change st₂_call.mem (nodesBase - 1) ≤ st₁_call.mem (nodesBase - 1) + 8 * L at hle₂
    omega
  · intro r hr
    have hne : r ≠ 12 := Nat.ne_of_lt hr
    simp [st₂, st₁, Function.update_of_ne hne]
  · exact memAgree_slotZero_of_lctFrame (le_trans (by decide) hnb) h0 hlct₀₂

theorem double_zigZig_exec {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    {st : State} (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : st.mem (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1))
    (hz : ZeroFrom st.mem (st.mem (nodesBase - 1)))
    (hhp_lt : st.mem (nodesBase - 1) + 16 * L < 2 ^ w)
    (h0 : SlotZeroOk st.mem nodesBase)
    {t : AuxTree} {pp x p_id : ℕ}
    (ht : TreeMemMatch w h L st.mem nodesBase cap t 0 pp) (hnd : t.toList.Nodup)
    (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) (hp : p_id = t.parentIn x 0)
    (hclean : ∀ u ∈ t.pathTo x,
      revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0)
    (hr0 : st.regs 0 = nodesBase) (hr1 : st.regs 1 = x) (hr4 : st.regs 4 = p_id)
    (ω : ℕ → Bool) :
    ∃ st' c,
      Runs w p ω
        (Stmt.call 12 sp.rotate [.reg 0, .reg 4] ;;
         Stmt.call 12 sp.rotate [.reg 0, .reg 1]) st .normal st' c ∧
      c + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ 2 * K_ROTATE L + 10 ∧
      st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L ∧
      (∀ r < 12, st'.regs r = st.regs r) ∧
      SlotZeroOk st'.mem nodesBase ∧
      TreeMemMatch w h L st'.mem nodesBase cap ((t.rotateAt p_id).rotateAt x) 0 pp ∧
      ((t.rotateAt p_id).rotateAt x).toList.Perm t.toList ∧
      ((t.rotateAt p_id).rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag st.mem nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L ((t.rotateAt p_id).rotateAt x) false 0 =
        evalMemSteps st.mem nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      (∀ u ∈ ((t.rotateAt p_id).rotateAt x).pathTo x,
        revFlag st'.mem nodesBase u = false ∧ nodeField st'.mem nodesBase u OFF_HAS_TAG = 0) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st.mem st'.mem := by
  have hp_mem : p_id ∈ t.toList := hp ▸ (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hx hxr).1
  have hp_path : p_id ∈ t.pathTo x :=
    hp ▸ AuxTree.mem_pathTo_parent hnd hx (AuxTree.self_mem_pathTo hx) hxr
  exact double_pair_exec p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0
    ht hnd hx hp_mem hp_path hclean (by decide) hr0 hr1 hr4 ω

theorem double_zigZag_exec {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    {st : State} (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : st.mem (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1))
    (hz : ZeroFrom st.mem (st.mem (nodesBase - 1)))
    (hhp_lt : st.mem (nodesBase - 1) + 16 * L < 2 ^ w)
    (h0 : SlotZeroOk st.mem nodesBase)
    {t : AuxTree} {pp x : ℕ}
    (ht : TreeMemMatch w h L st.mem nodesBase cap t 0 pp) (hnd : t.toList.Nodup)
    (hx : x ∈ t.toList)
    (hclean : ∀ u ∈ t.pathTo x,
      revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0)
    (hr0 : st.regs 0 = nodesBase) (hr1 : st.regs 1 = x)
    (ω : ℕ → Bool) :
    ∃ st' c,
      Runs w p ω
        (Stmt.call 12 sp.rotate [.reg 0, .reg 1] ;;
         Stmt.call 12 sp.rotate [.reg 0, .reg 1]) st .normal st' c ∧
      c + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ 2 * K_ROTATE L + 10 ∧
      st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L ∧
      (∀ r < 12, st'.regs r = st.regs r) ∧
      SlotZeroOk st'.mem nodesBase ∧
      TreeMemMatch w h L st'.mem nodesBase cap ((t.rotateAt x).rotateAt x) 0 pp ∧
      ((t.rotateAt x).rotateAt x).toList.Perm t.toList ∧
      ((t.rotateAt x).rotateAt x).evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag st.mem nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L ((t.rotateAt x).rotateAt x) false 0 =
        evalMemSteps st.mem nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      (∀ u ∈ ((t.rotateAt x).rotateAt x).pathTo x,
        revFlag st'.mem nodesBase u = false ∧ nodeField st'.mem nodesBase u OFF_HAS_TAG = 0) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st.mem st'.mem :=
  double_pair_exec p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0
    ht hnd hx hx (AuxTree.self_mem_pathTo hx) hclean (by decide) hr0 hr1 hr1 ω

/-- Execute one double splay step (zig-zig or zig-zag) when `g_id ≠ 0`. -/
theorem splayDouble_exec {w h L nodesBase cap : ℕ} (p : Program) (sp : SplayProcs)
    {st : State} (hp_ok : SplayProgramOk w h p sp)
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hnb : 3 ≤ nodesBase) (hL_hdr : st.mem (nodesBase - 3) = L)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ st.mem (nodesBase - 1))
    (hz : ZeroFrom st.mem (st.mem (nodesBase - 1)))
    (hhp_lt : st.mem (nodesBase - 1) + 16 * L < 2 ^ w)
    (h0 : SlotZeroOk st.mem nodesBase)
    {t : AuxTree} {pp x : ℕ}
    (ht : TreeMemMatch w h L st.mem nodesBase cap t 0 pp) (hnd : t.toList.Nodup)
    (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) (hpr : t.parentIn x 0 ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x,
      revFlag st.mem nodesBase u = false ∧ nodeField st.mem nodesBase u OFF_HAS_TAG = 0)
    (hr0 : st.regs 0 = nodesBase) (hr1 : st.regs 1 = x)
    (hr4 : st.regs 4 = t.parentIn x 0)
    (hr5 : st.regs 5 = nodesBase + NODE_STRIDE * t.parentIn x 0)
    (hr6 : st.regs 6 = t.parentIn (t.parentIn x 0) 0)
    (ω : ℕ → Bool) :
    ∃ st' c t',
      Runs w p ω
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
        st .normal st' c ∧
      c + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ 2 * K_ROTATE L + 50 ∧
      st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) ∧
      st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L ∧
      st'.regs 0 = nodesBase ∧
      st'.regs 1 = x ∧
      st'.regs 3 = st.regs 3 ∧
      SlotZeroOk st'.mem nodesBase ∧
      TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp ∧
      t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag st.mem nodesBase) false ∧
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps st.mem nodesBase h L t false 0 ∧
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      (∀ u ∈ t'.pathTo x,
        revFlag st'.mem nodesBase u = false ∧ nodeField st'.mem nodesBase u OFF_HAS_TAG = 0) ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st.mem st'.mem ∧
      2 ≤ t.depthOf x ∧
      t'.depthOf x = t.depthOf x - 2 ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
          t.treePhi vSize + 3 * (t'.findSubtree x).rank vSize) := by
  let p_id := t.parentIn x 0
  let g_id := t.parentIn p_id 0
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at hbase ⊢; omega
  have hw1 : 1 < 2 ^ w := by unfold NODE_STRIDE at hbase; omega
  have hp_mem : p_id ∈ t.toList := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hx hxr).1
  have hg_mem : g_id ∈ t.toList := (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hpr).1
  have hx12 := ht.nodup_perm_mem hx
  have hp12 := ht.nodup_perm_mem hp_mem
  have hg12 := ht.nodup_perm_mem hg_mem
  let ptrG := nodesBase + NODE_STRIDE * g_id
  let gLeft := nodeField st.mem nodesBase g_id OFF_LEFT
  let pLeft := nodeField st.mem nodesBase p_id OFF_LEFT
  let b1 := if p_id = gLeft then 1 else 0
  let b2 := if x = pLeft then 1 else 0
  have ha7 : (nodePtrExpr 0 6).eval w st = some ptrG :=
    eval_nodePtrExpr hstride hr0 hr6 (nodePtr_lt_pow hbase hg12.2)
  let st7 : State := { st with regs := Function.update st.regs 7 ptrG }
  have hr7_7 : st7.regs 7 = ptrG := by simp [st7]
  have ha8 : (fieldLoadExpr 7 OFF_LEFT).eval w st7 = some gLeft := by
    simpa [nodeField, gLeft, st7] using
      eval_fieldLoadExpr hr7_7 (nodeAddr_lt_pow hbase hg12.2 (by decide))
  let st8 : State := { st7 with regs := Function.update st7.regs 8 gLeft }
  have hr8_5 : st8.regs 5 = nodesBase + NODE_STRIDE * p_id := by simp [st8, st7, hr5, p_id]
  have ha9 : (fieldLoadExpr 5 OFF_LEFT).eval w st8 = some pLeft := by
    simpa [nodeField, pLeft, st8, st7] using
      eval_fieldLoadExpr hr8_5 (nodeAddr_lt_pow hbase hp12.2 (by decide))
  let st9 : State := { st8 with regs := Function.update st8.regs 9 pLeft }
  have ha10 : (Expr.bin .eq (.reg 4) (.reg 8)).eval w st9 = some b1 :=
    Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [st9, st8, st7, hr4, p_id]))
      (Expr.eval_reg_of_eq (by simp [st9, st8])) hw1
  let st10 : State := { st9 with regs := Function.update st9.regs 10 b1 }
  have ha11 : (Expr.bin .eq (.reg 1) (.reg 9)).eval w st10 = some b2 :=
    Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [st10, st9, st8, st7, hr1]))
      (Expr.eval_reg_of_eq (by simp [st10, st9])) hw1
  let st11 : State := { st10 with regs := Function.update st10.regs 11 b2 }
  have hr11_0 : st11.regs 0 = nodesBase := by simp [st11, st10, st9, st8, st7, hr0]
  have hr11_1 : st11.regs 1 = x := by simp [st11, st10, st9, st8, st7, hr1]
  have hr11_3 : st11.regs 3 = st.regs 3 := by simp [st11, st10, st9, st8, st7]
  have hr11_4 : st11.regs 4 = p_id := by simp [st11, st10, st9, st8, st7, hr4, p_id]
  have h10_11 : (Expr.bin .eq (.reg 10) (.reg 11)).eval w st11 = some (if b1 = b2 then 1 else 0) :=
    Expr.eval_eq_op (Expr.eval_reg_of_eq (by simp [st11, st10]))
      (Expr.eval_reg_of_eq (by simp [st11])) hw1
  let condStmt : Stmt :=
    Stmt.cond (.bin .eq (.reg 10) (.reg 11))
      (Stmt.call 12 sp.rotate [.reg 0, .reg 4] ;;
       Stmt.call 12 sp.rotate [.reg 0, .reg 1])
      (Stmt.call 12 sp.rotate [.reg 0, .reg 1] ;;
       Stmt.call 12 sp.rotate [.reg 0, .reg 1])
  have wrapPrefix : ∀ {st' : State} {c_exec : ℕ} {t' : AuxTree},
      Runs w p ω condStmt st11 .normal st' c_exec →
      c_exec + (st'.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ 2 * K_ROTATE L + 14 →
      st.mem (nodesBase - 1) ≤ st'.mem (nodesBase - 1) →
      st'.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L →
      st'.regs 0 = nodesBase → st'.regs 1 = x → st'.regs 3 = st.regs 3 →
      SlotZeroOk st'.mem nodesBase →
      TreeMemMatch w h L st'.mem nodesBase cap t' 0 pp →
      t'.toList.Perm t.toList →
      t'.evalInorder (revFlag st'.mem nodesBase) false =
        t.evalInorder (revFlag st.mem nodesBase) false →
      evalMemSteps st'.mem nodesBase h L t' false 0 =
        evalMemSteps st.mem nodesBase h L t false 0 →
      (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) →
      (∀ u ∈ t'.pathTo x,
        revFlag st'.mem nodesBase u = false ∧ nodeField st'.mem nodesBase u OFF_HAS_TAG = 0) →
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nodesBase u off = nodeField st.mem nodesBase u off) →
      LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
        (nodesBase - 1) st.mem st'.mem →
      2 ≤ t.depthOf x ∧ t'.depthOf x = t.depthOf x - 2 ∧
        (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
          t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
            t.treePhi vSize + 3 * (t'.findSubtree x).rank vSize) →
      ∃ st'' c'' t'',
        Runs w p ω
          (Stmt.assign 7 (nodePtrExpr 0 6) ;;
           Stmt.assign 8 (fieldLoadExpr 7 OFF_LEFT) ;;
           Stmt.assign 9 (fieldLoadExpr 5 OFF_LEFT) ;;
           Stmt.assign 10 (.bin .eq (.reg 4) (.reg 8)) ;;
           Stmt.assign 11 (.bin .eq (.reg 1) (.reg 9)) ;;
           Stmt.cond (.bin .eq (.reg 10) (.reg 11))
             (Stmt.call 12 sp.rotate [.reg 0, .reg 4] ;;
              Stmt.call 12 sp.rotate [.reg 0, .reg 1])
             (Stmt.call 12 sp.rotate [.reg 0, .reg 1] ;;
              Stmt.call 12 sp.rotate [.reg 0, .reg 1])) st .normal st'' c'' ∧
        c'' + (st''.mem (nodesBase - 1) - st.mem (nodesBase - 1)) ≤ 2 * K_ROTATE L + 50 ∧
        st.mem (nodesBase - 1) ≤ st''.mem (nodesBase - 1) ∧
        st''.mem (nodesBase - 1) ≤ st.mem (nodesBase - 1) + 16 * L ∧
        st''.regs 0 = nodesBase ∧ st''.regs 1 = x ∧ st''.regs 3 = st.regs 3 ∧
        SlotZeroOk st''.mem nodesBase ∧
        TreeMemMatch w h L st''.mem nodesBase cap t'' 0 pp ∧
        t''.toList.Perm t.toList ∧
        t''.evalInorder (revFlag st''.mem nodesBase) false =
          t.evalInorder (revFlag st.mem nodesBase) false ∧
        evalMemSteps st''.mem nodesBase h L t'' false 0 =
          evalMemSteps st.mem nodesBase h L t false 0 ∧
        (∀ u ≤ cap, ∀ off, IsNonStructNonAggOff off →
          nodeField st''.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
        (∀ u ∈ t''.pathTo x,
          revFlag st''.mem nodesBase u = false ∧ nodeField st''.mem nodesBase u OFF_HAS_TAG = 0) ∧
        (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
          nodeField st''.mem nodesBase u off = nodeField st.mem nodesBase u off) ∧
        LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
          (nodesBase - 1) st.mem st''.mem ∧
        2 ≤ t.depthOf x ∧ t''.depthOf x = t.depthOf x - 2 ∧
        (∀ vSize, t''.treeSize vSize = t.treeSize vSize ∧
          t''.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
            t.treePhi vSize + 3 * (t''.findSubtree x).rank vSize) := by
    intro st' c_exec t' hcond hc_e hge hle hr0' hr1' hr3' h0' ht' hpm' hev' hst' hns' hcl' hout' hlct' hlift
    refine ⟨st', 6 + (5 + (5 + (4 + (4 + c_exec + 1) + 1) + 1) + 1) + 1, t', ?_,
      by omega, hge, hle, hr0', hr1', hr3', h0', ht', hpm', hev', hst', hns', hcl', hout', hlct',
      hlift.1, hlift.2.1, hlift.2.2⟩
    exact runs_seq_iff.mpr (Or.inr ⟨st7, 6, _, runs_assign_iff.mpr ⟨ptrG, ha7, rfl, rfl, rfl⟩,
      runs_seq_iff.mpr (Or.inr ⟨st8, 5, _, runs_assign_iff.mpr ⟨gLeft, ha8, rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨st9, 5, _, runs_assign_iff.mpr ⟨pLeft, ha9, rfl, rfl, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨st10, 4, _, runs_assign_iff.mpr ⟨b1, ha10, rfl, rfl, rfl⟩,
            runs_seq_iff.mpr (Or.inr ⟨st11, 4, _, runs_assign_iff.mpr ⟨b2, ha11, rfl, rfl, rfl⟩,
              hcond, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hsub_g_nd : (t.findSubtree g_id).toList.Nodup := AuxTree.findSubtree_nodup hnd
  have ht_g := AuxTree.findSubtree_match ht hg_mem
  rcases AuxTree.grandparent_child_cases (p := p_id) (g := g_id) hnd hx hxr rfl hp_mem hpr rfl with
    ⟨A, B, C, D, hs⟩ | ⟨A, B, C, D, hs⟩ | ⟨A, B, C, D, hs⟩ | ⟨A, B, C, D, hs⟩
  all_goals
    rw [hs] at hsub_g_nd ht_g
    have hnd_g := hsub_g_nd
    rcases nodup_node_unfold hsub_g_nd with ⟨hL_nd, hg_nL, hR_nd, hdisj_g⟩
    rcases tmm_children ht_g with ⟨hg_L0', _, hg_Lm, hg_Rm⟩
  · -- Case 1: Zig-zig right `(.node g (.node p (.node x A B) C) D)`
    have hb1 : b1 = 1 := by simp only [b1, gLeft, hg_L0', AuxTree.rootId, ↓reduceIte]
    have hb2 : b2 = 1 := by simp only [b2, pLeft, (tmm_children hg_Lm).1, AuxTree.rootId, ↓reduceIte]
    rcases double_zigZig_exec p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 (st := st11)
        ht hnd hx hxr rfl hclean hr11_0 hr11_1 hr11_4 ω with
      ⟨st', c_exec, hr_exec, hc_exec, hge, hle, hreg', h0', ht', hperm', heval', hsteps',
       hns', hclean', hout', hlct'⟩
    have hcond : Runs w p ω condStmt st11 .normal st' (3 + c_exec + 1) :=
      runs_cond_iff.mpr ⟨1, c_exec, by simpa [hb1, hb2] using h10_11, by simpa using hr_exec, rfl⟩
    let s' := ((t.findSubtree g_id).rotateAt p_id).rotateAt x
    have hgp : g_id ≠ p_id := fun h => hg_nL (mem_node_of_eq h)
    have hp_in_s : p_id ∈ (t.findSubtree g_id).toList := by rw [hs]; exact mem_node_left_of_eq rfl
    have hs1 : (t.findSubtree g_id).rotateAt p_id ≠ .leaf :=
      AuxTree.rotateAt_ne_leaf (by rw [hs]; simp)
    have hs1_perm : ((t.findSubtree g_id).rotateAt p_id).toList.Perm (t.findSubtree g_id).toList :=
      AuxTree.rotateAt_toList_perm p_id _
    have hx_in_s1 : x ∈ ((t.findSubtree g_id).rotateAt p_id).toList :=
      hs1_perm.mem_iff.2 (by rw [hs]; simp [AuxTree.toList])
    have hs1_root : ((t.findSubtree g_id).rotateAt p_id).rootId = p_id := by
      rw [hs, AuxTree.rotateAt_zigRight _ _ _ hgp]; rfl
    have hpx : x ≠ p_id := by
      rcases nodup_node_unfold hL_nd with ⟨_, hp_nx, _, _⟩
      exact fun h => hp_nx (mem_node_of_eq h.symm)
    have ht_eq_rep : (t.rotateAt p_id).rotateAt x = t.replaceSubtree g_id s' := by
      rw [AuxTree.rotateAt_of_ancestor hnd hg_mem hp_in_s hgp.symm,
          AuxTree.rotateAt_replaceSubtree hnd hg_mem hs1 hs1_perm hx_in_s1 (hs1_root.symm ▸ hpx)]
    have hs'_prop : ∀ vSize, s' = .node x A (.node p_id B (.node g_id C D)) ∧
        (t.findSubtree g_id).findSubtree x = .node x A B ∧
        s'.treeSize vSize = (t.findSubtree g_id).treeSize vSize ∧
        s'.treePhi vSize + 3 * (AuxTree.node x A B).rank vSize + 1 ≤
          (t.findSubtree g_id).treePhi vSize + 3 * s'.rank vSize := fun vSize => by
      have h := AuxTree.double_zigZig_right vSize g_id p_id x A B C D hnd_g
      dsimp only at h; dsimp only [s']; rwa [hs]
    have hs'_ne : s' ≠ .leaf := by rw [(hs'_prop (fun _ => 0)).1]; simp
    have hs'_root : s'.rootId = x := by rw [(hs'_prop (fun _ => 0)).1]; rfl
    have hstep_lift := AuxTree.doubleStep_lift (p := p_id) (g := g_id) hnd hx hxr rfl hp_mem hpr rfl hg_mem
      hs'_ne hs'_root ((AuxTree.rotateAt_toList_perm x _).trans hs1_perm) fun vSize => by
        rcases hs'_prop vSize with ⟨_, hfx, hsz, hphi⟩
        have hx_sub := AuxTree.findSubtree_findSubtree (p := x) hnd hg_mem (by rw [hs]; simp [AuxTree.toList])
        rw [hx_sub] at hfx; rw [hfx]; exact ⟨hsz, hphi⟩
    rw [← ht_eq_rep] at hstep_lift
    exact wrapPrefix hcond (by dsimp only [st11, st10, st9, st8, st7] at hc_exec; omega) hge hle
      ((hreg' 0 (by decide)).trans hr11_0) ((hreg' 1 (by decide)).trans hr11_1)
      ((hreg' 3 (by decide)).trans hr11_3) h0' ht' hperm' heval' hsteps' hns' hclean' hout' hlct' hstep_lift
  · -- Case 2: Zig-zag left-right `(.node g (.node p A (.node x B C)) D)`
    have hx_nA : x ∉ A.toList := by
      rcases nodup_node_unfold hL_nd with ⟨_, _, _, hdisj_p⟩
      exact fun h => hdisj_p x (Or.inl h) (by simp [AuxTree.toList])
    have hA_ne_x : A.rootId ≠ x := by
      cases A with
      | leaf => simp [AuxTree.rootId]; omega
      | node a l r => exact rootId_ne_of_not_mem hx_nA a l r rfl
    have hb1 : b1 = 1 := by simp only [b1, gLeft, hg_L0', AuxTree.rootId, ↓reduceIte]
    have hb2 : b2 = 0 := by simp only [b2, pLeft, (tmm_children hg_Lm).1, hA_ne_x.symm, ↓reduceIte]
    rcases double_zigZag_exec p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 (st := st11)
        ht hnd hx hclean hr11_0 hr11_1 ω with
      ⟨st', c_exec, hr_exec, hc_exec, hge, hle, hreg', h0', ht', hperm', heval', hsteps',
       hns', hclean', hout', hlct'⟩
    have hcond : Runs w p ω condStmt st11 .normal st' (3 + c_exec + 1) :=
      runs_cond_iff.mpr ⟨0, c_exec, by simpa [hb1, hb2] using h10_11, by simpa using hr_exec, rfl⟩
    let s' := ((t.findSubtree g_id).rotateAt x).rotateAt x
    have hs'_prop : ∀ vSize, s' = .node x (.node p_id A B) (.node g_id C D) ∧
        (t.findSubtree g_id).findSubtree x = .node x B C ∧
        s'.treeSize vSize = (t.findSubtree g_id).treeSize vSize ∧
        s'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
          (t.findSubtree g_id).treePhi vSize + 3 * s'.rank vSize := fun vSize => by
      have h := AuxTree.double_zigZag_lr vSize g_id p_id x A B C D hnd_g
      dsimp only at h; dsimp only [s']; rwa [hs]
    have hgx : g_id ≠ x := fun h => hg_nL (mem_node_right_of_eq h)
    have hx_in_s : x ∈ (t.findSubtree g_id).toList := by rw [hs]; simp [AuxTree.toList]
    have hpx : p_id ≠ x := by
      rcases nodup_node_unfold hL_nd with ⟨_, _, _, hdisj_p⟩
      exact fun h => hdisj_p p_id (Or.inr rfl) (mem_node_of_eq h)
    have hA_x : A = .leaf ∨ A.rootId ≠ x := by
      cases A with | leaf => exact Or.inl rfl | node _ _ _ => exact Or.inr hA_ne_x
    have hl_child : ∀ lx l1 l2, AuxTree.node p_id A (.node x B C) = .node lx l1 l2 → lx ≠ x := by
      intro lx l1 l2 h; cases h; exact hpx
    have hx_nD : x ∉ D.toList := fun h => hdisj_g x (Or.inl (by simp [AuxTree.toList])) h
    have hs1_eq : (t.findSubtree g_id).rotateAt x = .node g_id (.node x (.node p_id A B) C) D := by
      rw [hs, AuxTree.rotateAt_recurse_left hgx hl_child (rootId_ne_of_not_mem hx_nD) (by simp [AuxTree.toList]),
          AuxTree.rotateAt_zigLeft A B C hpx hA_x]
    have hs1_ne : (t.findSubtree g_id).rotateAt x ≠ .leaf := by rw [hs1_eq]; simp
    have hs1_perm : ((t.findSubtree g_id).rotateAt x).toList.Perm (t.findSubtree g_id).toList :=
      AuxTree.rotateAt_toList_perm x _
    have hs1_root : ((t.findSubtree g_id).rotateAt x).rootId = g_id := by rw [hs1_eq]; rfl
    have ht_eq_rep : (t.rotateAt x).rotateAt x = t.replaceSubtree g_id s' := by
      rw [AuxTree.rotateAt_of_ancestor hnd hg_mem hx_in_s hgx.symm,
          AuxTree.rotateAt_replaceSubtree hnd hg_mem hs1_ne hs1_perm (hs1_perm.mem_iff.2 hx_in_s) (hs1_root.symm ▸ hgx.symm)]
    have hs'_ne : s' ≠ .leaf := by rw [(hs'_prop (fun _ => 0)).1]; simp
    have hs'_root : s'.rootId = x := by rw [(hs'_prop (fun _ => 0)).1]; rfl
    have hstep_lift := AuxTree.doubleStep_lift (p := p_id) (g := g_id) hnd hx hxr rfl hp_mem hpr rfl hg_mem
      hs'_ne hs'_root ((AuxTree.rotateAt_toList_perm x _).trans hs1_perm) fun vSize => by
        rcases hs'_prop vSize with ⟨_, hfx, hsz, hphi⟩
        have hx_sub := AuxTree.findSubtree_findSubtree hnd hg_mem hx_in_s
        rw [hx_sub] at hfx; rw [hfx]; exact ⟨hsz, hphi⟩
    rw [← ht_eq_rep] at hstep_lift
    exact wrapPrefix hcond (by dsimp only [st11, st10, st9, st8, st7] at hc_exec; omega) hge hle
      ((hreg' 0 (by decide)).trans hr11_0) ((hreg' 1 (by decide)).trans hr11_1)
      ((hreg' 3 (by decide)).trans hr11_3) h0' ht' hperm' heval' hsteps' hns' hclean' hout' hlct' hstep_lift
  · -- Case 3: Zig-zag right-left `(.node g A (.node p (.node x B C) D))`
    have hp_nA : p_id ∉ A.toList :=
      fun h => hdisj_g p_id (Or.inl h) (by dsimp only [p_id]; simp [AuxTree.toList])
    have hA_ne_p : A.rootId ≠ p_id := by
      cases A with
      | leaf => simp [AuxTree.rootId]; omega
      | node a l r => exact rootId_ne_of_not_mem hp_nA a l r rfl
    have hb1 : b1 = 0 := by simp only [b1, gLeft, hg_L0', hA_ne_p.symm, ↓reduceIte]
    have hb2 : b2 = 1 := by simp only [b2, pLeft, (tmm_children hg_Rm).1, AuxTree.rootId, ↓reduceIte]
    rcases double_zigZag_exec p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 (st := st11)
        ht hnd hx hclean hr11_0 hr11_1 ω with
      ⟨st', c_exec, hr_exec, hc_exec, hge, hle, hreg', h0', ht', hperm', heval', hsteps',
       hns', hclean', hout', hlct'⟩
    have hcond : Runs w p ω condStmt st11 .normal st' (3 + c_exec + 1) :=
      runs_cond_iff.mpr ⟨0, c_exec, by simpa [hb1, hb2] using h10_11, by simpa using hr_exec, rfl⟩
    let s' := ((t.findSubtree g_id).rotateAt x).rotateAt x
    have hs'_prop : ∀ vSize, s' = .node x (.node g_id A B) (.node p_id C D) ∧
        (t.findSubtree g_id).findSubtree x = .node x B C ∧
        s'.treeSize vSize = (t.findSubtree g_id).treeSize vSize ∧
        s'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
          (t.findSubtree g_id).treePhi vSize + 3 * s'.rank vSize := fun vSize => by
      have h := AuxTree.double_zigZag_rl vSize g_id p_id x A B C D hnd_g
      dsimp only at h; dsimp only [s']; rwa [hs]
    have hgx : g_id ≠ x := fun h => hdisj_g g_id (Or.inr rfl) (mem_node_left_of_eq h)
    have hx_in_s : x ∈ (t.findSubtree g_id).toList := by rw [hs]; simp [AuxTree.toList]
    have hx_nA : x ∉ A.toList := fun h => hdisj_g x (Or.inl h) (by simp [AuxTree.toList])
    have hpx : p_id ≠ x := by
      rcases nodup_node_unfold hR_nd with ⟨_, hp_nx, _, _⟩
      exact fun h => hp_nx (mem_node_of_eq h)
    have hr_child : ∀ rx r1 r2, AuxTree.node p_id (.node x B C) D = .node rx r1 r2 → rx ≠ x := by
      intro rx r1 r2 h; cases h; exact hpx
    have hs1_eq : (t.findSubtree g_id).rotateAt x = .node g_id A (.node x B (.node p_id C D)) := by
      rw [hs, AuxTree.rotateAt_recurse_right hgx (rootId_ne_of_not_mem hx_nA) hr_child hx_nA (by simp),
          AuxTree.rotateAt_zigRight B C D hpx]
    have hs1_ne : (t.findSubtree g_id).rotateAt x ≠ .leaf := by rw [hs1_eq]; simp
    have hs1_perm : ((t.findSubtree g_id).rotateAt x).toList.Perm (t.findSubtree g_id).toList :=
      AuxTree.rotateAt_toList_perm x _
    have hs1_root : ((t.findSubtree g_id).rotateAt x).rootId = g_id := by rw [hs1_eq]; rfl
    have ht_eq_rep : (t.rotateAt x).rotateAt x = t.replaceSubtree g_id s' := by
      rw [AuxTree.rotateAt_of_ancestor hnd hg_mem hx_in_s hgx.symm,
          AuxTree.rotateAt_replaceSubtree hnd hg_mem hs1_ne hs1_perm (hs1_perm.mem_iff.2 hx_in_s) (hs1_root.symm ▸ hgx.symm)]
    have hs'_ne : s' ≠ .leaf := by rw [(hs'_prop (fun _ => 0)).1]; simp
    have hs'_root : s'.rootId = x := by rw [(hs'_prop (fun _ => 0)).1]; rfl
    have hstep_lift := AuxTree.doubleStep_lift (p := p_id) (g := g_id) hnd hx hxr rfl hp_mem hpr rfl hg_mem
      hs'_ne hs'_root ((AuxTree.rotateAt_toList_perm x _).trans hs1_perm) fun vSize => by
        rcases hs'_prop vSize with ⟨_, hfx, hsz, hphi⟩
        have hx_sub := AuxTree.findSubtree_findSubtree hnd hg_mem hx_in_s
        rw [hx_sub] at hfx; rw [hfx]; exact ⟨hsz, hphi⟩
    rw [← ht_eq_rep] at hstep_lift
    exact wrapPrefix hcond (by dsimp only [st11, st10, st9, st8, st7] at hc_exec; omega) hge hle
      ((hreg' 0 (by decide)).trans hr11_0) ((hreg' 1 (by decide)).trans hr11_1)
      ((hreg' 3 (by decide)).trans hr11_3) h0' ht' hperm' heval' hsteps' hns' hclean' hout' hlct' hstep_lift
  · -- Case 4: Zig-zig left `(.node g A (.node p B (.node x C D)))`
    have hp_nA : p_id ∉ A.toList :=
      fun h => hdisj_g p_id (Or.inl h) (by dsimp only [p_id]; simp [AuxTree.toList])
    have hx_nB : x ∉ B.toList := by
      rcases nodup_node_unfold hR_nd with ⟨_, _, _, hdisj_p⟩
      exact fun h => hdisj_p x (Or.inl h) (by simp [AuxTree.toList])
    have hA_ne_p : A.rootId ≠ p_id := by
      cases A with
      | leaf => simp [AuxTree.rootId]; omega
      | node a l r => exact rootId_ne_of_not_mem hp_nA a l r rfl
    have hB_ne_x : B.rootId ≠ x := by
      cases B with
      | leaf => simp [AuxTree.rootId]; omega
      | node b l r => exact rootId_ne_of_not_mem hx_nB b l r rfl
    have hb1 : b1 = 0 := by simp only [b1, gLeft, hg_L0', hA_ne_p.symm, ↓reduceIte]
    have hb2 : b2 = 0 := by simp only [b2, pLeft, (tmm_children hg_Rm).1, hB_ne_x.symm, ↓reduceIte]
    rcases double_zigZig_exec p sp hp_ok hbase hnb hL_hdr harena hz hhp_lt h0 (st := st11)
        ht hnd hx hxr rfl hclean hr11_0 hr11_1 hr11_4 ω with
      ⟨st', c_exec, hr_exec, hc_exec, hge, hle, hreg', h0', ht', hperm', heval', hsteps',
       hns', hclean', hout', hlct'⟩
    have hcond : Runs w p ω condStmt st11 .normal st' (3 + c_exec + 1) :=
      runs_cond_iff.mpr ⟨1, c_exec, by simpa [hb1, hb2] using h10_11, by simpa using hr_exec, rfl⟩
    let s' := ((t.findSubtree g_id).rotateAt p_id).rotateAt x
    have hs'_prop : ∀ vSize, s' = .node x (.node p_id (.node g_id A B) C) D ∧
        (t.findSubtree g_id).findSubtree x = .node x C D ∧
        s'.treeSize vSize = (t.findSubtree g_id).treeSize vSize ∧
        s'.treePhi vSize + 3 * (AuxTree.node x C D).rank vSize + 1 ≤
          (t.findSubtree g_id).treePhi vSize + 3 * s'.rank vSize := fun vSize => by
      have h := AuxTree.double_zigZig_left vSize g_id p_id x A B C D hnd_g
      dsimp only at h; dsimp only [s']; rwa [hs]
    have hgp : g_id ≠ p_id := fun h => hdisj_g g_id (Or.inr rfl) (mem_node_of_eq h)
    have hp_in_s : p_id ∈ (t.findSubtree g_id).toList := by rw [hs]; exact mem_node_right_of_eq rfl
    have hA_p : A = .leaf ∨ A.rootId ≠ p_id := by
      cases A with | leaf => exact Or.inl rfl | node _ _ _ => exact Or.inr hA_ne_p
    have hs1_eq : (t.findSubtree g_id).rotateAt p_id = .node p_id (.node g_id A B) (.node x C D) := by
      rw [hs, AuxTree.rotateAt_zigLeft A B (.node x C D) hgp hA_p]
    have hs1_ne : (t.findSubtree g_id).rotateAt p_id ≠ .leaf := by rw [hs1_eq]; simp
    have hs1_perm : ((t.findSubtree g_id).rotateAt p_id).toList.Perm (t.findSubtree g_id).toList :=
      AuxTree.rotateAt_toList_perm p_id _
    have hs1_root : ((t.findSubtree g_id).rotateAt p_id).rootId = p_id := by rw [hs1_eq]; rfl
    have hpx : x ≠ p_id := by
      rcases nodup_node_unfold hR_nd with ⟨_, _, _, hdisj_p⟩
      exact fun h => hdisj_p p_id (Or.inr rfl) (mem_node_of_eq h.symm)
    have ht_eq_rep : (t.rotateAt p_id).rotateAt x = t.replaceSubtree g_id s' := by
      rw [AuxTree.rotateAt_of_ancestor hnd hg_mem hp_in_s hgp.symm,
          AuxTree.rotateAt_replaceSubtree hnd hg_mem hs1_ne hs1_perm (hs1_perm.mem_iff.2 (by rw [hs]; simp [AuxTree.toList])) (hs1_root.symm ▸ hpx)]
    have hs'_ne : s' ≠ .leaf := by rw [(hs'_prop (fun _ => 0)).1]; simp
    have hs'_root : s'.rootId = x := by rw [(hs'_prop (fun _ => 0)).1]; rfl
    have hstep_lift := AuxTree.doubleStep_lift (p := p_id) (g := g_id) hnd hx hxr rfl hp_mem hpr rfl hg_mem
      hs'_ne hs'_root ((AuxTree.rotateAt_toList_perm x _).trans hs1_perm) fun vSize => by
        rcases hs'_prop vSize with ⟨_, hfx, hsz, hphi⟩
        have hx_sub := AuxTree.findSubtree_findSubtree (p := x) hnd hg_mem (by rw [hs]; simp [AuxTree.toList])
        rw [hx_sub] at hfx; rw [hfx]; exact ⟨hsz, hphi⟩
    rw [← ht_eq_rep] at hstep_lift
    exact wrapPrefix hcond (by dsimp only [st11, st10, st9, st8, st7] at hc_exec; omega) hge hle
      ((hreg' 0 (by decide)).trans hr11_0) ((hreg' 1 (by decide)).trans hr11_1)
      ((hreg' 3 (by decide)).trans hr11_3) h0' ht' hperm' heval' hsteps' hns' hclean' hout' hlct' hstep_lift

end

end MinCostFlow.LinkCut.Prog
