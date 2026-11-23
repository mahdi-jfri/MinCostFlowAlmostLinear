module

public import MinCostFlow.LinkCut.Prog.MathForestRerootPhi

/-!
# `lctRerootBody` Word-RAM Specification

Defines `C_REROOT_OP` and proves `lctRerootBody_runs` for `lctRerootBody lp` (`expose(nb, v + 1)`
followed by `revNode(nb, v + 1)`):
- preserves `LctExposeInvs`, `SafeMem`, and `LctFrame`;
- makes `v + 1` the root of its represented tree (`lctAuxParent ... (v + 1) = 0`,
  `OFF_PPAR = 0`, and `rootAbove` connected components preserved);
- satisfies amortized potential bound
  `c + Δhp + lctPhi' ≤ lctPhi + C_REROOT_OP L * (Nat.log 2 (n + 2) + 1)`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

/-- Per-reroot amortized constant (covers `expose`, `revNode`, and `O(log n)` newly heavy dashed
roots created along the reversed solid path). -/
def C_REROOT_OP (L : ℕ) : ℕ :=
  160000 * (L + 1)

theorem c_reroot_op_budget_le (L n : ℕ) :
    C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) + C_HEAVY L * (Nat.log 2 (n + 2) + 2) +
        K_REV_NODE + 20 ≤
      C_REROOT_OP L * (Nat.log 2 (n + 2) + 1) := by
  have hc_heavy := c_heavy_le L
  have hlog_ge : 1 ≤ Nat.log 2 (n + 2) + 1 := by omega
  have h1 : C_HEAVY L * (Nat.log 2 (n + 2) + 2) ≤
      2 * (8200 * (L + 1)) * (Nat.log 2 (n + 2) + 1) := by
    have hmul : C_HEAVY L * (Nat.log 2 (n + 2) + 2) ≤
        8200 * (L + 1) * (2 * (Nat.log 2 (n + 2) + 1)) :=
      Nat.mul_le_mul hc_heavy (by omega)
    calc
      C_HEAVY L * (Nat.log 2 (n + 2) + 2)
        ≤ 8200 * (L + 1) * (2 * (Nat.log 2 (n + 2) + 1)) := hmul
      _ = 2 * (8200 * (L + 1)) * (Nat.log 2 (n + 2) + 1) := by ring
  have h2 : K_REV_NODE + 20 ≤ 400 * (L + 1) * (Nat.log 2 (n + 2) + 1) := by
    unfold K_REV_NODE
    have hpos : 320 ≤ 400 * (L + 1) := by omega
    exact le_trans hpos (Nat.le_mul_of_pos_right _ hlog_ge)
  have h3 : C_EXPOSE_OP L = 140000 * (L + 1) := rfl
  have h4 : C_REROOT_OP L * (Nat.log 2 (n + 2) + 1) =
      (140000 * (L + 1) + 2 * (8200 * (L + 1)) + 400 * (L + 1) + 3200 * (L + 1)) *
        (Nat.log 2 (n + 2) + 1) := by
    unfold C_REROOT_OP
    ring
  rw [h3, h4, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

theorem c_expose_le_c_reroot (L : ℕ) : C_EXPOSE_OP L ≤ C_REROOT_OP L := by
  unfold C_EXPOSE_OP C_REROOT_OP
  omega

/-- Full Word-RAM specification for `lctRerootBody lp`: runs `expose(nb, v + 1)` and
`revNode(nb, v + 1)`, returning `0`, preserving `LctExposeInvs`, `SafeMem`, and `LctFrame`,
making `v + 1` the root of its represented tree, preserving `rootAbove` components, and
satisfying the amortized potential bound `C_REROOT_OP L * (Nat.log 2 (n + 2) + 1)`. -/
theorem lctRerootBody_runs {w h L P b n v hp0 pos : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)} {trees₀ : List AuxTree}
    (p : Program) (lp : LctProcs) (mem_safe mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hlp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hz0_safe : SlotZeroOk mem_safe (lctNodesBase b))
    (harena_safe : lctArenaHi b (lctCap n) ≤ hp0)
    (hsafe₀ : SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 mem₀)
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees₀ mem₀)
    (hv : v < n)
    (_hz₀ : ZeroFrom mem₀ (mem₀ (lctNodesBase b - 1)))
    (hedge_lt : ∀ p ∈ edgeMap, p.2.u < n ∧ p.2.v < n)
    (hslot_cover : ∀ u, n + 1 ≤ u → u ≤ lctCap n → u ∈ freeEdges ∨ ∃ p ∈ edgeMap, p.1 = u)
    (hhp_bd : mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
      C_REROOT_OP L * (Nat.log 2 (n + 2) + 1) + 7000 * (L + 1) * (n + 2) < 2 ^ w) :
    ∀ ω, ∃ st' c l_fin rest_fin,
      Runs w p ω (lctRerootBody lp) (startState [lctNodesBase b, v + 1] mem₀ pos) (.returned 0) st' c ∧
      LctExposeInvs w h L P b n freeEdges edgeMap
        (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) st'.mem ∧
      SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 st'.mem ∧
      LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1))
        (lctNodesBase b - 1) mem₀ st'.mem ∧
      nodeField st'.mem (lctNodesBase b) (v + 1) OFF_PPAR = 0 ∧
      lctAuxParent st'.mem (lctNodesBase b) (lctCap n) (v + 1) = 0 ∧
      (∀ x y, 1 ≤ x → x ≤ lctCap n → 1 ≤ y → y ≤ lctCap n →
        (rootAbove (lctAuxParent st'.mem (lctNodesBase b) (lctCap n)) (lctCap n) x =
          rootAbove (lctAuxParent st'.mem (lctNodesBase b) (lctCap n)) (lctCap n) y ↔
         rootAbove (lctAuxParent mem₀ (lctNodesBase b) (lctCap n)) (lctCap n) x =
          rootAbove (lctAuxParent mem₀ (lctNodesBase b) (lctCap n)) (lctCap n) y)) ∧
      RootMove (lctAuxParent mem₀ (lctNodesBase b) (lctCap n))
        (lctAuxParent st'.mem (lctNodesBase b) (lctCap n)) (lctCap n) (v + 1) ∧
      c + (st'.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st'.mem b n ≤
        lctPhi L mem₀ b n + C_REROOT_OP L * (Nat.log 2 (n + 2) + 1) := by
  intro ω
  have hexpose_bd : mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
      C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) + 7000 * (L + 1) * (n + 2) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (c_expose_le_c_reroot L)) _) _) hhp_bd
  rcases exposeBody_runs p lp.splay mem_safe mem₀ hp_base.splay_hasAt hlp_sp hp_base.splay_ok
      hz0_safe harena_safe hsafe₀ hi hv _hz₀ hexpose_bd ω with
    ⟨st₁, c₁, l_fin, rest_fin, hrun₁, hi₁, hsafe₁, hfr₁, hpar₁, hpp₁, _, _, hev₁, hphi₁⟩
  let r0 := (startState [lctNodesBase b, v + 1] mem₀ pos).regs
  let r₁ := Function.update r0 2 (v + 1)
  have hcall₁ : Runs w p ω (Stmt.call 2 lp.expose [.reg 0, .reg 1])
      (startState [lctNodesBase b, v + 1] mem₀ pos) .normal
      { mem := st₁.mem, regs := r₁, pos := st₁.pos } (2 + c₁ + 1) := by
    refine runs_call_iff.mpr ⟨[lctNodesBase b, v + 1], exposeBody lp.splay, .returned (v + 1), st₁, c₁,
      ?_, hexpose_eq, hrun₁, rfl, ?_, rfl⟩
    · simp [evalArgs, Expr.eval, startState]
    · cases st₁; rfl
  have hr1_0 : r₁ 0 = lctNodesBase b := by simp [r₁, r0, startState]
  have hr1_1 : r₁ 1 = v + 1 := by simp [r₁, r0, startState]
  have hbase₁ : lctNodesBase b + NODE_STRIDE * (lctCap n + 1) < 2 ^ w := by
    have h1 := hi₁.sf.2.2.2.1; have h2 := hi₁.sf.2.2.2.2.2.1; omega
  have ht1_match : TreeMemMatch w h L st₁.mem (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) l_fin AuxTree.leaf) 0 0 := by
    have hm := (hi₁.sf.2.2.2.2.2.2.2.2.2 (AuxTree.node (v + 1) l_fin AuxTree.leaf) (by simp)).2.2
    simpa [AuxTree.rootId, hpp₁] using hm
  have hnd_all₁ : ((AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap AuxTree.toList).Nodup :=
    hi₁.sf.2.2.2.2.2.2.2.2.1.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have ht1_nd : (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList.Nodup :=
    list_nodup_of_flatMap_nodup hnd_all₁ (by simp)
  rcases revNodeBody_subtree_runs st₁.pos hbase₁ ht1_match ht1_nd ω with
    ⟨st₂, c₂, hrun₂, hc₂, hm₂, hsteps₂, hev₂, hhp₂, hstat₂, hout_x₂, hout_arena₂⟩
  have hsafe₂ : SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 st₂.mem := by
    rcases hrun₂ with ⟨fuel₂, hex₂⟩
    dsimp only [AuxTree.rootId] at hex₂
    have hx_le : v + 1 ≤ lctCap n := by unfold lctCap; omega
    exact (revNode_safeExec hi₁.sf.2.2.1 harena_safe (st := startState [lctNodesBase b, v + 1] st₁.mem st₁.pos)
      hx_le rfl rfl hsafe₁ hex₂).2
  have hcall₂ : Runs w p ω (Stmt.call 2 lp.splay.revNode [.reg 0, .reg 1])
      { mem := st₁.mem, regs := r₁, pos := st₁.pos } .normal
      { mem := st₂.mem, regs := Function.update r₁ 2 0, pos := st₂.pos } (2 + c₂ + 1) := by
    refine runs_call_iff.mpr ⟨[lctNodesBase b, v + 1], revNodeBody, .returned 0, st₂, c₂,
      ?_, hp_base.splay_ok.revNode_eq, ?_, rfl, ?_, rfl⟩
    · simp [evalArgs, Expr.eval, hr1_0, hr1_1]
    · simpa [startState, AuxTree.rootId] using hrun₂
    · cases st₂; rfl
  let r₂ := Function.update r₁ 2 0
  have hret : Runs w p ω (Stmt.ret (.const 0))
      { mem := st₂.mem, regs := r₂, pos := st₂.pos } (.returned 0)
      { mem := st₂.mem, regs := r₂, pos := st₂.pos } 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
  have hrun_full := runs_seq_normal hcall₁ (runs_seq_normal hcall₂ hret)
  have hfr₂ : LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1))
      (lctNodesBase b - 1) st₁.mem st₂.mem :=
    lctFrame_of_memPreservedOutside hout_arena₂ (by unfold NODE_STRIDE; omega)
      hi₁.sf.2.2.2.1 hi₁.sf.2.2.2.2.2.2.1
  have hfr_all := lctFrame_trans hfr₁ hfr₂
  rcases revNode_reroot_invs hi₁ hv hpp₁ hev₁ hm₂ hsteps₂ hev₂ hhp₂ hstat₂ hout_x₂
      hedge_lt hslot_cover with
    ⟨hi₂, hpp₂, hpar₂_v, hcomp₁₂, hmove₁₂, hphi₂_le⟩
  have hcomp_all : ∀ x y, 1 ≤ x → x ≤ lctCap n → 1 ≤ y → y ≤ lctCap n →
      (rootAbove (lctAuxParent st₂.mem (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent st₂.mem (lctNodesBase b) (lctCap n)) (lctCap n) y ↔
       rootAbove (lctAuxParent mem₀ (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent mem₀ (lctNodesBase b) (lctCap n)) (lctCap n) y) := by
    intro x y hx1 hx2 hy1 hy2
    rw [hcomp₁₂ x y hx1 hx2 hy1 hy2]
    have hfun : lctAuxParent st₁.mem (lctNodesBase b) (lctCap n) =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap n) := funext hpar₁
    rw [hfun]
  have hbudget := c_reroot_op_budget_le L n
  refine ⟨{ mem := st₂.mem, regs := r₂, pos := st₂.pos }, _, l_fin, rest_fin,
    hrun_full, hi₂, hsafe₂, hfr_all, hpp₂, hpar₂_v, hcomp_all, ?_, ?_⟩
  · have hfun : lctAuxParent st₁.mem (lctNodesBase b) (lctCap n) =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap n) := funext hpar₁
    rw [← hfun]; exact hmove₁₂
  change 2 + c₁ + 1 + (2 + c₂ + 1 + 2 + 1) + 1 +
      (st₂.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st₂.mem b n ≤
    lctPhi L mem₀ b n + C_REROOT_OP L * (Nat.log 2 (n + 2) + 1)
  rw [hhp₂]
  clear hmove₁₂ hi hsafe₀ hi₁ hsafe₁ hi₂ hsafe₂ hfr₁ hfr₂ hfr_all hrun₁ hrun₂ hcall₁ hcall₂ hret hrun_full
    hp_base hz0_safe hhp_bd hexpose_bd hbase₁ ht1_match hnd_all₁ ht1_nd
  omega

end MinCostFlow.LinkCut.Prog
