module

public import MinCostFlow.LinkCut.Prog.MathForestExposeIter

/-!
# Expose Loop and Full `exposeBody` Word-RAM Specification

Proves `exposeLoop_runs` (by induction on `lctCap n - t_y.treeSize`) and `exposeBody_runs`,
establishing `t_fin = .node (v + 1) l_fin .leaf`, `OFF_PPAR = 0`, `OFF_REV = 0`,
`OFF_HAS_TAG = 0`, `LctExposeInvs`, `LctFrame`, `SafeMem`, preserved `lctAuxParent`, and
total amortized cost + heap growth `≤ C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1)`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

theorem exposeLoop_runs {w h L P b n v hp0 pos BUDGET : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    (m : ℕ) (p : Program) (sp : SplayProcs) (mem_safe mem₀ : ℕ → ℕ) (r₀ : ℕ → ℕ)
    {t_y : AuxTree} {rest₀ : List AuxTree}
    (hp_has : p.HasAt sp.numZero (splayBodies sp h))
    (hp_base : ∃ spB, sp = SplayProcs.atBase spB)
    (hp_ok : SplayProgramOk w h p sp)
    (hz0_safe : SlotZeroOk mem_safe (lctNodesBase b))
    (harena_safe : lctArenaHi b (lctCap n) ≤ hp0)
    (hsafe₀ : SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 mem₀)
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (t_y :: rest₀) mem₀)
    (hv : v < n)
    (hz₀ : ZeroFrom mem₀ (mem₀ (lctNodesBase b - 1)))
    (hy_ne : t_y ≠ .leaf)
    (hy_last : (t_y.evalInorder (revFlag mem₀ (lctNodesBase b)) false).getLast? = some (v + 1))
    (hr0_0 : r₀ 0 = lctNodesBase b) (hr0_1 : r₀ 1 = v + 1)
    (hr0_5 : r₀ 5 = t_y.rootId)
    (hr0_6 : r₀ 6 = nodeField mem₀ (lctNodesBase b) t_y.rootId OFF_PPAR)
    (hbudget_w : BUDGET < 2 ^ w)
    (hhp_inv : mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
      (3 * K_SPLAY_STEP L + M_EXPOSE L) *
        (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n))) +
      6000 * (L + 1) * (n + 2) ≤ BUDGET)
    (hm : lctCap n - t_y.treeSize (lctVSize mem₀ (lctNodesBase b) (lctCap n)) ≤ m) :
    ∀ ω, ∃ st_end c_end t_end rest_end,
      Runs w p ω
        (Stmt.loop (.reg 6) (Stmt.call 10 sp.splay [.reg 0, .reg 6] ;; exposeIterSpliceStmt sp))
        { mem := mem₀, regs := r₀, pos := pos } .normal st_end c_end ∧
      LctExposeInvs w h L P b n freeEdges edgeMap (t_end :: rest_end) st_end.mem ∧
      SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 st_end.mem ∧
      LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1))
        (lctNodesBase b - 1) mem₀ st_end.mem ∧
      (∀ u, lctAuxParent st_end.mem (lctNodesBase b) (lctCap n) u =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap n) u) ∧
      t_end ≠ .leaf ∧
      nodeField st_end.mem (lctNodesBase b) t_end.rootId OFF_PPAR = 0 ∧
      st_end.regs 0 = lctNodesBase b ∧ st_end.regs 1 = v + 1 ∧
      (t_end.evalInorder (revFlag st_end.mem (lctNodesBase b)) false).getLast? = some (v + 1) ∧
      st_end.mem (lctNodesBase b - 1) + lctPhi L st_end.mem b n + 6000 * (L + 1) * (n + 2) ≤ BUDGET ∧
      c_end + (st_end.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st_end.mem b n ≤
        lctPhi L mem₀ b n +
          (3 * K_SPLAY_STEP L + M_EXPOSE L) *
            (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n))) + 10 := by
  induction m generalizing mem₀ r₀ pos t_y rest₀ with
  | zero =>
      intro ω
      by_cases hpp0 : nodeField mem₀ (lctNodesBase b) t_y.rootId OFF_PPAR = 0
      · have hrun0 : Runs w p ω
            (Stmt.loop (.reg 6) (Stmt.call 10 sp.splay [.reg 0, .reg 6] ;; exposeIterSpliceStmt sp))
            { mem := mem₀, regs := r₀, pos := pos } .normal
            { mem := mem₀, regs := r₀, pos := pos } ((Expr.reg 6).size + 1) :=
          runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr0_6, hpp0], rfl, rfl, rfl⟩)
        refine ⟨_, _, t_y, rest₀, hrun0, hi, hsafe₀,
          lctFrame_refl (by have := hi.sf.2.2.1; unfold NODE_STRIDE; omega) hi.sf.2.2.2.1 hz₀,
          fun _ => rfl, hy_ne, hpp0, hr0_0, hr0_1, hy_last, ?_, ?_⟩
        · exact le_trans (Nat.add_le_add (Nat.le_add_right _ _) (Nat.le_refl _)) hhp_inv
        · simp only [Expr.size, Nat.sub_self, Nat.add_zero]
          have h2le : 1 + 1 + 0 + lctPhi L mem₀ b n ≤ lctPhi L mem₀ b n + 10 := by omega
          exact le_trans h2le (Nat.add_le_add_right (Nat.le_add_right _ _) 10)
      · rcases exposeIter_runs (pos := pos) p sp mem_safe mem₀ r₀ hp_has hp_base hp_ok hz0_safe harena_safe hsafe₀
            hi hv hz₀ hy_ne hy_last hpp0 hr0_0 hr0_1 hr0_5 hr0_6 hbudget_w hhp_inv ω with
          ⟨st₁, c₁, t_next, rest₁, _, hi₁, _, _, _, _, _, _, _, _, _, hgrow, _⟩
        have hcap_le := treeSize_le_cap_of_invs hi₁.sf hi₁.subdivOk.1 hi₁.auxPathOk (t := t_next) (by simp)
        clear hi hsafe₀ hi₁; omega
  | succ m ih =>
      intro ω
      by_cases hpp0 : nodeField mem₀ (lctNodesBase b) t_y.rootId OFF_PPAR = 0
      · have hrun0 : Runs w p ω
            (Stmt.loop (.reg 6) (Stmt.call 10 sp.splay [.reg 0, .reg 6] ;; exposeIterSpliceStmt sp))
            { mem := mem₀, regs := r₀, pos := pos } .normal
            { mem := mem₀, regs := r₀, pos := pos } ((Expr.reg 6).size + 1) :=
          runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr0_6, hpp0], rfl, rfl, rfl⟩)
        refine ⟨_, _, t_y, rest₀, hrun0, hi, hsafe₀,
          lctFrame_refl (by have := hi.sf.2.2.1; unfold NODE_STRIDE; omega) hi.sf.2.2.2.1 hz₀,
          fun _ => rfl, hy_ne, hpp0, hr0_0, hr0_1, hy_last, ?_, ?_⟩
        · exact le_trans (Nat.add_le_add (Nat.le_add_right _ _) (Nat.le_refl _)) hhp_inv
        · simp only [Expr.size, Nat.sub_self, Nat.add_zero]
          have h2le : 1 + 1 + 0 + lctPhi L mem₀ b n ≤ lctPhi L mem₀ b n + 10 := by omega
          exact le_trans h2le (Nat.add_le_add_right (Nat.le_add_right _ _) 10)
      · rcases exposeIter_runs (pos := pos) p sp mem_safe mem₀ r₀ hp_has hp_base hp_ok hz0_safe harena_safe hsafe₀
            hi hv hz₀ hy_ne hy_last hpp0 hr0_0 hr0_1 hr0_5 hr0_6 hbudget_w hhp_inv ω with
          ⟨st₁, c₁, t_next, rest₁, hrun₁, hi₁, hsafe₁, hfr₁, hpar₁, hne₁, hr1_0, hr1_1, hr1_5, hr1_6,
            hlast₁, hgrow₁, hpot₁⟩
        have hcap_le := treeSize_le_cap_of_invs hi₁.sf hi₁.subdivOk.1 hi₁.auxPathOk (t := t_next) (by simp)
        have hm₁ : lctCap n - t_next.treeSize (lctVSize st₁.mem (lctNodesBase b) (lctCap n)) ≤ m := by
          clear hi hsafe₀ hi₁ hsafe₁ hfr₁ hrun₁ hhp_inv hpot₁; omega
        have hmem_le₁ : mem₀ (lctNodesBase b - 1) ≤ st₁.mem (lctNodesBase b - 1) := hfr₁.2.2.1
        have hhp_inv₁ : st₁.mem (lctNodesBase b - 1) + lctPhi L st₁.mem b n +
            (3 * K_SPLAY_STEP L + M_EXPOSE L) *
              (Nat.log 2 (n + 2) + 1 - t_next.rank (lctVSize st₁.mem (lctNodesBase b) (lctCap n))) +
            6000 * (L + 1) * (n + 2) ≤ BUDGET := by
          have hsub_le : (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st₁.mem b n +
              (3 * K_SPLAY_STEP L + M_EXPOSE L) *
                (Nat.log 2 (n + 2) + 1 - t_next.rank (lctVSize st₁.mem (lctNodesBase b) (lctCap n))) ≤
              lctPhi L mem₀ b n +
                (3 * K_SPLAY_STEP L + M_EXPOSE L) *
                  (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n))) := by
            have h0 : (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) ≤
                c₁ + 2 + (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) :=
              Nat.le_add_left _ _
            exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right h0 _) _) hpot₁
          have hM1 : st₁.mem (lctNodesBase b - 1) =
              mem₀ (lctNodesBase b - 1) + (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) :=
            (Nat.add_sub_of_le hmem_le₁).symm
          calc st₁.mem (lctNodesBase b - 1) + lctPhi L st₁.mem b n +
                (3 * K_SPLAY_STEP L + M_EXPOSE L) *
                  (Nat.log 2 (n + 2) + 1 - t_next.rank (lctVSize st₁.mem (lctNodesBase b) (lctCap n))) +
                6000 * (L + 1) * (n + 2)
            _ = mem₀ (lctNodesBase b - 1) + ((st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) +
                  lctPhi L st₁.mem b n +
                  (3 * K_SPLAY_STEP L + M_EXPOSE L) *
                    (Nat.log 2 (n + 2) + 1 - t_next.rank (lctVSize st₁.mem (lctNodesBase b) (lctCap n)))) +
                6000 * (L + 1) * (n + 2) := by nth_rw 1 [hM1]; simp only [Nat.add_assoc]
            _ ≤ mem₀ (lctNodesBase b - 1) + (lctPhi L mem₀ b n +
                  (3 * K_SPLAY_STEP L + M_EXPOSE L) *
                    (Nat.log 2 (n + 2) + 1 - t_y.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n)))) +
                6000 * (L + 1) * (n + 2) :=
                Nat.add_le_add_right (Nat.add_le_add_left hsub_le _) _
            _ ≤ BUDGET := by simpa only [Nat.add_assoc] using hhp_inv
        rcases ih (pos := st₁.pos) st₁.mem st₁.regs hsafe₁ hi₁ hfr₁.2.2.2.2.1 hne₁ hlast₁
            hr1_0 hr1_1 hr1_5 hr1_6 hhp_inv₁ hm₁ ω with
          ⟨st_end, c_end, t_end, rest_end, hrun_rest, hi_end, hsafe_end, hfr_end, hpar_end,
            hne_end, hpp_end, hr_e0, hr_e1, hlast_end, hbd_end, hpot_end⟩
        have hloop_all : Runs w p ω
            (Stmt.loop (.reg 6) (Stmt.call 10 sp.splay [.reg 0, .reg 6] ;; exposeIterSpliceStmt sp))
            { mem := mem₀, regs := r₀, pos := pos } .normal st_end
            ((Expr.reg 6).size + c₁ + c_end + 1) := by
          refine runs_loop_iff.mpr (Or.inr (Or.inr ⟨nodeField mem₀ (lctNodesBase b) t_y.rootId OFF_PPAR,
            st₁, c₁, c_end, ?_, hpp0, hrun₁, ?_, rfl⟩))
          · simp [Expr.eval, hr0_6]
          · have hst₁_eq : st₁ = { mem := st₁.mem, regs := st₁.regs, pos := st₁.pos } := by
              cases st₁; rfl
            rw [← hst₁_eq] at hrun_rest; exact hrun_rest
        have hdiff_hp : st_end.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1) =
            (st_end.mem (lctNodesBase b - 1) - st₁.mem (lctNodesBase b - 1)) +
            (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) := by
          have h2 : st₁.mem (lctNodesBase b - 1) ≤ st_end.mem (lctNodesBase b - 1) := hfr_end.2.2.1
          clear hi hsafe₀ hi₁ hsafe₁ hi_end hsafe_end hfr₁ hfr_end hrun₁ hrun_rest hloop_all
          omega
        refine ⟨st_end, _, t_end, rest_end, hloop_all, hi_end, hsafe_end, lctFrame_trans hfr₁ hfr_end,
          fun u => (hpar_end u).trans (hpar₁ u), hne_end, hpp_end, hr_e0, hr_e1, hlast_end, hbd_end, ?_⟩
        simp only [Expr.size]
        clear hi hsafe₀ hi₁ hsafe₁ hi_end hsafe_end hfr₁ hfr_end hpar₁ hpar_end hrun₁ hrun_rest hloop_all
        omega

private theorem k_pull_4L_le (L n : ℕ) : K_PULL L + 4 * L ≤ 6000 * (L + 1) * (n + 2) := by
  unfold K_PULL
  have h1 : 800 * (L + 1) + 4 * L ≤ 6000 * (L + 1) := by omega
  exact le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))

theorem exposeBody_runs {w h L P b n v hp0 pos : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)} {trees₀ : List AuxTree}
    (p : Program) (sp : SplayProcs) (mem_safe mem₀ : ℕ → ℕ)
    (hp_has : p.HasAt sp.numZero (splayBodies sp h))
    (hp_base : ∃ spB, sp = SplayProcs.atBase spB)
    (hp_ok : SplayProgramOk w h p sp)
    (hz0_safe : SlotZeroOk mem_safe (lctNodesBase b))
    (harena_safe : lctArenaHi b (lctCap n) ≤ hp0)
    (hsafe₀ : SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 mem₀)
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees₀ mem₀)
    (hv : v < n)
    (_hz₀ : ZeroFrom mem₀ (mem₀ (lctNodesBase b - 1)))
    (hhp_bd : mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
      C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) + 7000 * (L + 1) * (n + 2) < 2 ^ w) :
    ∀ ω, ∃ st' c l_fin rest_fin,
      Runs w p ω (exposeBody sp) (startState [lctNodesBase b, v + 1] mem₀ pos) (.returned (v + 1)) st' c ∧
      LctExposeInvs w h L P b n freeEdges edgeMap (.node (v + 1) l_fin .leaf :: rest_fin) st'.mem ∧
      SafeMem mem_safe (lctNodesBase b) (lctCap n) hp0 st'.mem ∧
      LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1))
        (lctNodesBase b - 1) mem₀ st'.mem ∧
      (∀ u, lctAuxParent st'.mem (lctNodesBase b) (lctCap n) u =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap n) u) ∧
      nodeField st'.mem (lctNodesBase b) (v + 1) OFF_PPAR = 0 ∧
      revFlag st'.mem (lctNodesBase b) (v + 1) = false ∧
      nodeField st'.mem (lctNodesBase b) (v + 1) OFF_HAS_TAG = 0 ∧
      (AuxTree.node (v + 1) l_fin .leaf).evalInorder (revFlag st'.mem (lctNodesBase b)) false =
        l_fin.evalInorder (revFlag st'.mem (lctNodesBase b)) false ++ [v + 1] ∧
      c + (st'.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st'.mem b n ≤
        lctPhi L mem₀ b n + C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) := by
  intro ω
  have hx1 : 1 ≤ v + 1 := by omega
  have hcap_def : lctCap n = 2 * n := rfl
  have hx2 : v + 1 ≤ lctCap n := by rw [hcap_def]; omega
  rcases hi.sf.tree_of_mem hx1 hx2 with ⟨t₀, rest₀, ht_perm₀, hx_in₀⟩
  have ht₀_free : t₀.rootId ∉ freeEdges := fun hfm => by
    rcases hi.freeNodeOk t₀.rootId hfm with ⟨hn1, _, htr, _⟩
    have hmem_t0 : t₀ ∈ trees₀ := ht_perm₀.symm.subset (by simp)
    have heq := unique_tree_of_mem
      (hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
      hmem_t0 htr (AuxTree.rootId_mem_toList (hi.sf.trees_ok t₀ hmem_t0).1)
      (by simp [AuxTree.toList])
    rw [heq, AuxTree.toList] at hx_in₀
    simp only [List.mem_append, List.mem_singleton] at hx_in₀
    rcases hx_in₀ with (h | heq_id) | h
    · exact absurd h List.not_mem_nil
    · have hlt : v + 1 < n + 1 := Nat.succ_lt_succ hv
      rw [heq_id] at hlt
      exact Nat.not_le_of_lt hlt hn1
    · exact absurd h List.not_mem_nil
  have h6_7 : 6000 * (L + 1) * (n + 2) ≤ 7000 * (L + 1) * (n + 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hroom₀ : mem₀ (lctNodesBase b - 1) + 6000 * (L + 1) * (n + 2) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h6_7) hhp_bd
  have hhp_sp1 : mem₀ (lctNodesBase b - 1) + K_PUSH_PATH L * (t₀.depthOf (v + 1) + 1) +
      8 * L * t₀.depthOf (v + 1) < 2 ^ w :=
    splay_lct_tree_headroom_lt hi.sf rfl (ht_perm₀.symm.subset (by simp)) hx_in₀ hroom₀
  rcases splayForest_lct_runs p sp mem_safe mem₀ (lctNodesBase b) (lctCap n) hp0 pos hp_has hp_base hp_ok
      hz0_safe harena_safe hsafe₀ hi.sf ht_perm₀ hx_in₀ hhp_sp1 ω with
    ⟨st₁, c₁, t₁, hrun₁, hsf₁, hsafe₁, hr1_id, ht_perm_nodes, hev₁, hsteps₁,
      hrev₁, hht₁, hpp₁, hout₁, hstat₁, hfr₁, hphi₁_all⟩
  have hinv₁ := LctExposeInvs.of_splay hi ht_perm₀ ht₀_free hsf₁ hev₁ hsteps₁
    ht_perm_nodes (by simpa [hr1_id] using hpp₁) hout₁ hstat₁ hfr₁
  rcases hinv₁ with ⟨hi₁, hpar₁, _, hvs₁_fn, hheavy₁⟩
  cases ht₁_eq : t₁ with
  | leaf => exact absurd ht₁_eq (hi₁.sf.trees_ok t₁ (by simp)).1
  | node x' l₁ r₁ =>
      have hx'_eq : x' = v + 1 := by simpa [ht₁_eq, AuxTree.rootId] using hr1_id
      subst hx'_eq
      rw [ht₁_eq] at hsf₁ hi₁ hev₁ hsteps₁ ht_perm_nodes
      have hrev₁_val : nodeField st₁.mem (lctNodesBase b) (v + 1) OFF_REV = 0 := by
        simp only [revFlag, decide_eq_false_iff_not, not_not] at hrev₁; exact hrev₁
      let r0 := (startState [lctNodesBase b, v + 1] mem₀ pos).regs
      have hcall₁ : Runs w p ω (Stmt.call 10 sp.splay [.reg 0, .reg 1])
          (startState [lctNodesBase b, v + 1] mem₀ pos) .normal
          { mem := st₁.mem, regs := Function.update r0 10 (v + 1), pos := st₁.pos } (2 + c₁ + 1) := by
        refine runs_call_iff.mpr ⟨[lctNodesBase b, v + 1], splayBody sp, .returned (v + 1), st₁, c₁, ?_,
          hp_ok.splay_eq, hrun₁, rfl, ?_, rfl⟩
        · simp [evalArgs, Expr.eval, startState]
        · cases st₁; rfl
      let r₁_reg := Function.update r0 10 (v + 1)
      have hlog_t0 : t₀.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n)) ≤ Nat.log 2 (n + 2) + 1 :=
        treeRank_le_log_of_invs hi.sf hi.subdivOk.1 hi.auxPathOk (ht_perm₀.symm.subset (by simp))
      have hphi₁_le : c₁ + (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st₁.mem b n ≤
          lctPhi L mem₀ b n + 3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L := by
        have hp_sp := (hphi₁_all (lctVSize mem₀ (lctNodesBase b) (lctCap n))).2.2
        have hvs₁_eq : lctVSize st₁.mem (lctNodesBase b) (lctCap n) =
            lctVSize mem₀ (lctNodesBase b) (lctCap n) := funext hvs₁_fn
        have hmul_rk : 3 * K_SPLAY_STEP L * t₀.rank (lctVSize mem₀ (lctNodesBase b) (lctCap n)) ≤
            3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) :=
          Nat.mul_le_mul_left _ hlog_t0
        nth_rw 1 [← hvs₁_eq] at hp_sp
        unfold lctPhi; rw [hheavy₁] at *
        clear hi hsafe₀ hi₁ hsafe₁ hfr₁ hrun₁ hphi₁_all hhp_bd hroom₀ hhp_sp1 ht_perm₀ ht_perm_nodes hev₁ hsteps₁ hout₁ hstat₁
        omega
      let BUDGET := mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
        3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L +
        K_PULL L + C_HEAVY L + 100 +
        (3 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) +
        6000 * (L + 1) * (n + 2)
      have hbudget_lt : BUDGET ≤ mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
          C_EXPOSE_OP L * (Nat.log 2 (n + 2) + 1) + 7000 * (L + 1) * (n + 2) := by
        have hbd := expose_enter_loop_budget_le L n
        have hadd := Nat.add_le_add_left hbd (mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n)
        simpa only [BUDGET, Nat.add_assoc] using hadd
      have hbudget_w : BUDGET < 2 ^ w := lt_of_le_of_lt hbudget_lt hhp_bd
      have hph1_room : st₁.mem (lctNodesBase b - 1) + K_PULL L + 4 * L < 2 ^ w := by
        have h4L := k_pull_4L_le L n
        have hmem_ge : mem₀ (lctNodesBase b - 1) ≤ st₁.mem (lctNodesBase b - 1) := hfr₁.2.2.1
        have hlt_bd : st₁.mem (lctNodesBase b - 1) + K_PULL L + 4 * L ≤ BUDGET := by
          dsimp only [BUDGET]
          clear hi hsafe₀ hi₁ hsafe₁ hfr₁ hrun₁ hphi₁_all hhp_bd hbudget_w hroom₀ hhp_sp1 ht_perm₀ ht_perm_nodes hev₁ hsteps₁ hout₁ hstat₁
          omega
        exact lt_of_le_of_lt hlt_bd hbudget_w
      rcases exposePhase1_runs (pos := st₁.pos) p sp mem_safe st₁.mem r₁_reg hp_has hp_base hp_ok hz0_safe harena_safe
          hsafe₁ hi₁ hv hrev₁_val hht₁ hfr₁.2.2.2.2.1 hph1_room
          (by simp [r₁_reg, r0, startState]) (by simp [r₁_reg, r0, startState]) ω with
        ⟨st₂, c₂, hrun₂, hi₂, hsafe₂, hfr₂, hpar₂, _, hr2_0, hr2_1, hr2_5, hr2_6, _, hlast₂, _, hphi₂⟩
      let t_y0 := AuxTree.node (v + 1) l₁ .leaf
      let rest₂ := if r₁ = .leaf then rest₀ else r₁ :: rest₀
      have hi₂' : LctExposeInvs w h L P b n freeEdges edgeMap (t_y0 :: rest₂) st₂.mem := by
        cases r₁ <;> simpa [t_y0, rest₂] using hi₂
      have hinv_loop : st₂.mem (lctNodesBase b - 1) + lctPhi L st₂.mem b n +
          (3 * K_SPLAY_STEP L + M_EXPOSE L) *
            (Nat.log 2 (n + 2) + 1 - t_y0.rank (lctVSize st₂.mem (lctNodesBase b) (lctCap n))) +
          6000 * (L + 1) * (n + 2) ≤ BUDGET := by
        have hrk_bd : (3 * K_SPLAY_STEP L + M_EXPOSE L) *
            (Nat.log 2 (n + 2) + 1 - t_y0.rank (lctVSize st₂.mem (lctNodesBase b) (lctCap n))) ≤
            (3 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        have hmem_ge₁ : mem₀ (lctNodesBase b - 1) ≤ st₁.mem (lctNodesBase b - 1) := hfr₁.2.2.1
        have hmem_ge₂ : st₁.mem (lctNodesBase b - 1) ≤ st₂.mem (lctNodesBase b - 1) := hfr₂.2.2.1
        have hst1_bd : (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) + lctPhi L st₁.mem b n ≤
            lctPhi L mem₀ b n + 3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L :=
          le_trans (Nat.add_le_add_right (Nat.le_add_left _ c₁) _) hphi₁_le
        have hst2_bd : (st₂.mem (lctNodesBase b - 1) - st₁.mem (lctNodesBase b - 1)) + lctPhi L st₂.mem b n ≤
            lctPhi L st₁.mem b n + K_PULL L + C_HEAVY L + 80 :=
          le_trans (Nat.add_le_add_right (Nat.le_add_left _ c₂) _) hphi₂
        have hst1_eq : st₁.mem (lctNodesBase b - 1) =
            mem₀ (lctNodesBase b - 1) + (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) :=
          (Nat.add_sub_of_le hmem_ge₁).symm
        have hst2_eq : st₂.mem (lctNodesBase b - 1) =
            st₁.mem (lctNodesBase b - 1) + (st₂.mem (lctNodesBase b - 1) - st₁.mem (lctNodesBase b - 1)) :=
          (Nat.add_sub_of_le hmem_ge₂).symm
        have hsum_12 : st₂.mem (lctNodesBase b - 1) + lctPhi L st₂.mem b n ≤
            mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
              3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L +
              K_PULL L + C_HEAVY L + 100 := by
          have hst2_p : st₂.mem (lctNodesBase b - 1) + lctPhi L st₂.mem b n ≤
              st₁.mem (lctNodesBase b - 1) + lctPhi L st₁.mem b n + K_PULL L + C_HEAVY L + 80 := by
            rw [hst2_eq, Nat.add_assoc (st₁.mem _)]
            exact le_trans (Nat.add_le_add_left hst2_bd _) (by simp only [Nat.add_assoc, le_refl])
          have hst1_p : st₁.mem (lctNodesBase b - 1) + lctPhi L st₁.mem b n ≤
              mem₀ (lctNodesBase b - 1) + lctPhi L mem₀ b n +
                3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L := by
            rw [hst1_eq, Nat.add_assoc (mem₀ _)]
            simpa only [Nat.add_assoc] using Nat.add_le_add_left hst1_bd (mem₀ (lctNodesBase b - 1))
          exact le_trans hst2_p (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right hst1_p (K_PULL L)) (C_HEAVY L)) 100 |> fun h =>
            le_trans (Nat.add_le_add_left (by omega : 80 ≤ 100) _) h)
        exact Nat.add_le_add_right (Nat.add_le_add hsum_12 hrk_bd) _
      have hst₂_eq : st₂ = { mem := st₂.mem, regs := st₂.regs, pos := st₂.pos } := by cases st₂; rfl
      rcases exposeLoop_runs (pos := st₂.pos)
          (lctCap n - t_y0.treeSize (lctVSize st₂.mem (lctNodesBase b) (lctCap n)))
          p sp mem_safe st₂.mem st₂.regs hp_has hp_base hp_ok hz0_safe harena_safe hsafe₂ hi₂' hv
          hfr₂.2.2.2.2.1 (by simp [t_y0]) hlast₂ hr2_0 hr2_1 (by simpa [t_y0, AuxTree.rootId] using hr2_5)
          (by simpa [t_y0, AuxTree.rootId] using hr2_6) hbudget_w hinv_loop le_rfl ω with
        ⟨st₃, c₃, t₃, rest₃, hrun₃, hi₃, hsafe₃, hfr₃, hpar₃, hne₃, hpp₃, hr3_0, hr3_1,
          hlast₃, hbd₃, hpot₃⟩
      have hrun₃' : Runs w p ω
          (Stmt.loop (.reg 6) (Stmt.call 10 sp.splay [.reg 0, .reg 6] ;; exposeIterSpliceStmt sp))
          st₂ .normal st₃ c₃ := by rw [hst₂_eq]; exact hrun₃
      have hx_in_seq₃ : v + 1 ∈ t₃.evalInorder (revFlag st₃.mem (lctNodesBase b)) false :=
        List.mem_of_getLast? hlast₃
      have hx_in_t3 : v + 1 ∈ t₃.toList := (t₃.evalInorder_perm _ _).mem_iff.1 hx_in_seq₃
      have hroom₃ : st₃.mem (lctNodesBase b - 1) + 6000 * (L + 1) * (n + 2) < 2 ^ w :=
        lt_of_le_of_lt (Nat.add_le_add (Nat.le_add_right _ _) (Nat.le_refl _))
          (lt_of_le_of_lt hbd₃ hbudget_w)
      have hhp_sp3 : st₃.mem (lctNodesBase b - 1) + K_PUSH_PATH L * (t₃.depthOf (v + 1) + 1) +
          8 * L * t₃.depthOf (v + 1) < 2 ^ w :=
        splay_lct_tree_headroom_lt hi₃.sf rfl (by simp) hx_in_t3 hroom₃
      have ht3_free : t₃.rootId ∉ freeEdges := fun hfm => by
        rcases hi₃.freeNodeOk t₃.rootId hfm with ⟨hn1, _, htr, _⟩
        have heq := unique_tree_of_mem
          (hi₃.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
          (by simp) htr (AuxTree.rootId_mem_toList (hi₃.sf.trees_ok t₃ (by simp)).1)
          (by simp [AuxTree.toList])
        rw [heq, AuxTree.toList] at hx_in_t3
        simp only [List.mem_append, List.mem_singleton] at hx_in_t3
        rcases hx_in_t3 with (h | heq_id) | h
        · exact absurd h List.not_mem_nil
        · have hlt : v + 1 < n + 1 := Nat.succ_lt_succ hv
          rw [heq_id] at hlt
          exact Nat.not_le_of_lt hlt hn1
        · exact absurd h List.not_mem_nil
      rcases splayForest_lct_runs p sp mem_safe st₃.mem (lctNodesBase b) (lctCap n) hp0 st₃.pos
          hp_has hp_base hp_ok hz0_safe harena_safe hsafe₃ hi₃.sf (List.Perm.refl _) hx_in_t3 hhp_sp3 ω with
        ⟨st₄, c₄, t_fin, hrun₄, hsf₄, hsafe₄, hr4_id, ht4_perm, hev₄, hsteps₄,
          hrev₄, hht₄, hpp₄, hout₄, hstat₄, hfr₄, hphi₄_all⟩
      have hinv₄ := LctExposeInvs.of_splay hi₃ (List.Perm.refl _) ht3_free hsf₄ hev₄ hsteps₄
        ht4_perm (by simpa [hr4_id] using hpp₄) hout₄ hstat₄ hfr₄
      rcases hinv₄ with ⟨hi₄, hpar₄, _, hvs₄_fn, hheavy₄⟩
      cases htfin_eq : t_fin with
      | leaf => exact absurd htfin_eq (hi₄.sf.trees_ok t_fin (by simp)).1
      | node x4 l_fin r_fin =>
          have hx4_eq : x4 = v + 1 := by simpa [htfin_eq, AuxTree.rootId] using hr4_id
          subst hx4_eq
          rw [htfin_eq] at hi₄ hev₄
          have hr_fin_leaf : r_fin = .leaf := by
            by_cases hr_ne : r_fin = .leaf
            · exact hr_ne
            · have hseq_r_ne : r_fin.evalInorder (revFlag st₄.mem (lctNodesBase b)) false ≠ [] :=
                auxTree_eval_ne_nil_of_ne_leaf hr_ne
              have hlast4 : ((AuxTree.node (v + 1) l_fin r_fin).evalInorder
                  (revFlag st₄.mem (lctNodesBase b)) false).getLast? = some (v + 1) := by
                rw [hev₄]; exact hlast₃
              have hx_in_r : v + 1 ∈ r_fin.toList := by
                have hev_eq : (AuxTree.node (v + 1) l_fin r_fin).evalInorder
                      (revFlag st₄.mem (lctNodesBase b)) false =
                    (l_fin.evalInorder (revFlag st₄.mem (lctNodesBase b)) false ++ [v + 1]) ++
                      r_fin.evalInorder (revFlag st₄.mem (lctNodesBase b)) false := by
                  simp [AuxTree.evalInorder, hrev₄]
                rw [hev_eq, List.getLast?_append_of_ne_nil _ hseq_r_ne] at hlast4
                exact (r_fin.evalInorder_perm _ _).mem_iff.1 (List.mem_of_getLast? hlast4)
              have hnd4 : (AuxTree.node (v + 1) l_fin r_fin).toList.Nodup :=
                list_nodup_of_flatMap_nodup
                  (hi₄.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
                  (by simp)
              exact absurd hx_in_r (auxTree_nodup_id_nin_right hnd4)
          subst hr_fin_leaf
          have hcall₄ : Runs w p ω (Stmt.call 10 sp.splay [.reg 0, .reg 1]) st₃ .normal
              { mem := st₄.mem, regs := Function.update st₃.regs 10 (v + 1), pos := st₄.pos } (2 + c₄ + 1) := by
            refine runs_call_iff.mpr ⟨[lctNodesBase b, v + 1], splayBody sp, .returned (v + 1), st₄, c₄, ?_,
              hp_ok.splay_eq, ?_, rfl, ?_, rfl⟩
            · simp [evalArgs, Expr.eval, hr3_0, hr3_1]
            · simpa [startState, hr3_0, hr3_1] using hrun₄
            · cases st₄; rfl
          let r₄_reg := Function.update st₃.regs 10 (v + 1)
          have hr4_1 : r₄_reg 1 = v + 1 := by simp [r₄_reg, hr3_1]
          have hret_step : Runs w p ω (Stmt.ret (.reg 1))
              { mem := st₄.mem, regs := r₄_reg, pos := st₄.pos } (.returned (v + 1))
              { mem := st₄.mem, regs := r₄_reg, pos := st₄.pos } 2 :=
            runs_ret_iff.mpr ⟨v + 1, by simp [Expr.eval, hr4_1], rfl, rfl, rfl⟩
          have hseq_full := runs_seq_normal hcall₁ (runs_seq_normal hrun₂
            (runs_seq_normal hrun₃' (runs_seq_normal hcall₄ hret_step)))
          have hcond_full := (runs_cond_iff (w := w) (p := p) (ω := ω) (e := .reg 1)
              (t := Stmt.ret (.const 0)) (st := startState [lctNodesBase b, v + 1] mem₀ pos)).mpr
            ⟨v + 1, _, by simp [Expr.eval, startState],
              by simpa [show v + 1 ≠ 0 by omega] using hseq_full, rfl⟩
          have hcond_full' : Runs w p ω (exposeBody sp) (startState [lctNodesBase b, v + 1] mem₀ pos)
              (.returned (v + 1)) { mem := st₄.mem, regs := r₄_reg, pos := st₄.pos }
              ((Expr.reg 1).size +
                (2 + c₁ + 1 + (c₂ + (c₃ + (2 + c₄ + 1 + 2 + 1) + 1) + 1) + 1) + 1) :=
            hcond_full
          have hpp_zero : nodeField st₄.mem (lctNodesBase b) (v + 1) OFF_PPAR = 0 := by
            simpa [AuxTree.rootId, htfin_eq] using hpp₄.trans hpp₃
          have hev_fin : (AuxTree.node (v + 1) l_fin .leaf).evalInorder (revFlag st₄.mem (lctNodesBase b)) false =
              l_fin.evalInorder (revFlag st₄.mem (lctNodesBase b)) false ++ [v + 1] := by
            simp [AuxTree.evalInorder, hrev₄]
          have hfr_all := lctFrame_trans (lctFrame_trans (lctFrame_trans hfr₁ hfr₂) hfr₃) hfr₄
          have hpar_all : ∀ u, lctAuxParent st₄.mem (lctNodesBase b) (lctCap n) u =
              lctAuxParent mem₀ (lctNodesBase b) (lctCap n) u := fun u =>
            (hpar₄ u).trans ((hpar₃ u).trans ((hpar₂ u).trans (hpar₁ u)))
          have hlog_t3 : t₃.rank (lctVSize st₃.mem (lctNodesBase b) (lctCap n)) ≤ Nat.log 2 (n + 2) + 1 :=
            treeRank_le_log_of_invs hi₃.sf hi₃.subdivOk.1 hi₃.auxPathOk (by simp)
          have hphi₄_le : c₄ + (st₄.mem (lctNodesBase b - 1) - st₃.mem (lctNodesBase b - 1)) +
                lctPhi L st₄.mem b n ≤
              lctPhi L st₃.mem b n + 3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L := by
            have hp_sp := (hphi₄_all (lctVSize st₃.mem (lctNodesBase b) (lctCap n))).2.2
            have hvs₄_eq : lctVSize st₄.mem (lctNodesBase b) (lctCap n) =
                lctVSize st₃.mem (lctNodesBase b) (lctCap n) := funext hvs₄_fn
            have hmul_rk : 3 * K_SPLAY_STEP L * t₃.rank (lctVSize st₃.mem (lctNodesBase b) (lctCap n)) ≤
                3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) :=
              Nat.mul_le_mul_left _ hlog_t3
            nth_rw 1 [← hvs₄_eq] at hp_sp
            unfold lctPhi; rw [hheavy₄] at *
            clear hi hsafe₀ hi₁ hsafe₁ hi₂ hi₂' hsafe₂ hi₃ hsafe₃ hi₄ hsafe₄
              hfr₁ hfr₂ hfr₃ hfr₄ hrun₁ hrun₂ hrun₃ hrun₃' hrun₄ hhp_bd hbudget_w
            omega
          have hdiff_all : st₄.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1) =
              (st₄.mem (lctNodesBase b - 1) - st₃.mem (lctNodesBase b - 1)) +
              (st₃.mem (lctNodesBase b - 1) - st₂.mem (lctNodesBase b - 1)) +
              (st₂.mem (lctNodesBase b - 1) - st₁.mem (lctNodesBase b - 1)) +
              (st₁.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) := by
            have h1 := hfr₁.2.2.1; have h2 := hfr₂.2.2.1; have h3 := hfr₃.2.2.1; have h4 := hfr₄.2.2.1
            clear hi hsafe₀ hi₁ hsafe₁ hi₂ hi₂' hsafe₂ hi₃ hsafe₃ hi₄ hsafe₄
              hfr₁ hfr₂ hfr₃ hfr₄ hrun₁ hrun₂ hrun₃ hrun₃' hrun₄ hhp_bd hbudget_w
            omega
          have hrk_t0 : (3 * K_SPLAY_STEP L + M_EXPOSE L) *
              (Nat.log 2 (n + 2) + 1 - t_y0.rank (lctVSize st₂.mem (lctNodesBase b) (lctCap n))) ≤
              (3 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) :=
            Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          have htotal_bd := expose_total_budget_le L n
          have hm_bd : K_PULL L + C_SPLAY_CONST L ≤ M_EXPOSE L := by unfold M_EXPOSE; omega
          refine ⟨{ mem := st₄.mem, regs := r₄_reg, pos := st₄.pos }, _, l_fin, rest₃,
            hcond_full', hi₄, hsafe₄, hfr_all, hpar_all,
            hpp_zero, hrev₄, hht₄, hev_fin, ?_⟩
          simp only [Expr.size]
          have h9 : (9 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) =
              3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) +
              (3 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) +
              3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) := by
            rw [show 9 * K_SPLAY_STEP L + M_EXPOSE L =
                3 * K_SPLAY_STEP L + (3 * K_SPLAY_STEP L + M_EXPOSE L) + 3 * K_SPLAY_STEP L by omega,
              Nat.add_mul, Nat.add_mul]
          have hcomb : c₁ + c₂ + c₃ + c₄ + (st₄.mem (lctNodesBase b - 1) - mem₀ (lctNodesBase b - 1)) +
                lctPhi L st₄.mem b n + 20 ≤
              lctPhi L mem₀ b n +
                (9 * K_SPLAY_STEP L + M_EXPOSE L) * (Nat.log 2 (n + 2) + 1) +
                M_EXPOSE L + C_SPLAY_CONST L + C_HEAVY L + 200 := by
            clear hi hsafe₀ hi₁ hsafe₁ hi₂ hi₂' hsafe₂ hi₃ hsafe₃ hi₄ hsafe₄
              hfr₁ hfr₂ hfr₃ hfr₄ hrun₁ hrun₂ hrun₃ hrun₃' hrun₄ hhp_bd hbudget_w htotal_bd
            omega
          clear hi hsafe₀ hi₁ hsafe₁ hi₂ hi₂' hsafe₂ hi₃ hsafe₃ hi₄ hsafe₄
            hfr₁ hfr₂ hfr₃ hfr₄ hrun₁ hrun₂ hrun₃ hrun₃' hrun₄ hhp_bd hbudget_w
          omega

end MinCostFlow.LinkCut.Prog
