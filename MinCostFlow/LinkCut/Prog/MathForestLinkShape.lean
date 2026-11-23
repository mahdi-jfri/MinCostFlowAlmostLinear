module

public import MinCostFlow.LinkCut.Prog.MathForestPathAdd

/-!
# Shared splay wrapper and component facts for `link`

The shared splay invariant wrapper (`splay_expose_invs_runs`), memory weakening
(`link_safeMem_weaken`), and the facts that `u` and `v` lie in different trees
(`rerootExpose_link_runs`, `link_not_sameComp_disjoint`, `link_find_u_tree`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section SharedSplayAndWeaken

theorem log_lctCap_add_two_le_op (n : ℕ) :
    Nat.log 2 (lctCap n + 2) ≤ Nat.log 2 (n + 2) + 1 := by
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 2)
  have hlt2 : lctCap n + 2 < 2 ^ (Nat.log 2 (n + 2) + 2) := by
    have h2 : 2 ^ (Nat.log 2 (n + 2) + 2) = 2 * 2 ^ (Nat.log 2 (n + 2) + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    unfold lctCap
    omega
  exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) hlt2)

/-- Runs `splayBody lp.splay` at `[nb, x]` from a `LctExposeInvs` state and returns updated
`LctExposeInvs`, `SafeMem`, structural frame, `lctAuxParent`/`lctRepSize` preservation, and the
amortized `lctPhi` bound `≤ lctPhi + 3 * K_SPLAY_STEP L * (log(n+2)+1) + C_SPLAY_CONST L`. -/
theorem splay_expose_invs_runs {w h L P b n hp_safe pos : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)} {trees : List AuxTree}
    {t : AuxTree} {rest : List AuxTree} {x : ℕ}
    (p : Program) (lp : LctProcs) (mem_safe mem : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hz0_safe : SlotZeroOk mem_safe (lctNodesBase b))
    (harena_safe : lctNodesBase b + NODE_STRIDE * (lctCap n + 1) ≤ hp_safe)
    (hsafe : SafeMem mem_safe (lctNodesBase b) (lctCap n) hp_safe mem)
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees mem)
    (ht_perm : trees.Perm (t :: rest))
    (hx_in : x ∈ t.toList)
    (ht_free : t.rootId ∉ freeEdges)
    (hroom : mem (lctNodesBase b - 1) + 6000 * (L + 1) * (n + 2) < 2 ^ w)
    (ω : ℕ → Bool) :
    let nb := lctNodesBase b
    let cap := lctCap n
    ∃ st' c_sp t',
      Runs w p ω (splayBody lp.splay) (startState [nb, x] mem pos) (.returned x) st' c_sp ∧
      LctExposeInvs w h L P b n freeEdges edgeMap (t' :: rest) st'.mem ∧
      SafeMem mem_safe nb cap hp_safe st'.mem ∧
      t'.rootId = x ∧
      t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nb) false = t.evalInorder (revFlag mem nb) false ∧
      evalMemSteps st'.mem nb h L t' false 0 = evalMemSteps mem nb h L t false 0 ∧
      revFlag st'.mem nb x = false ∧
      nodeField st'.mem nb x OFF_HAS_TAG = 0 ∧
      nodeField st'.mem nb x OFF_PPAR = nodeField mem nb t.rootId OFF_PPAR ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nb u off = nodeField mem nb u off) ∧
      LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem st'.mem ∧
      (∀ u, lctAuxParent st'.mem nb cap u = lctAuxParent mem nb cap u) ∧
      (∀ z, lctRepSize st'.mem nb cap z = lctRepSize mem nb cap z) ∧
      c_sp + (st'.mem (nb - 1) - mem (nb - 1)) + lctPhi L st'.mem b n ≤
        lctPhi L mem b n + 3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L := by
  intro nb cap
  have ht_mem : t ∈ trees := ht_perm.symm.subset (by simp)
  have hhp_sp : mem (nb - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x < 2 ^ w :=
    splay_lct_tree_headroom_lt hi.sf rfl ht_mem hx_in hroom
  have harena_nb : nb + NODE_STRIDE * (cap + 1) ≤ hp_safe := by
    simpa [nb, cap, lctArenaHi] using harena_safe
  rcases splayForest_lct_credit_runs p lp.splay mem_safe mem nb cap hp_safe pos
      hp_base.splay_hasAt hp_sp hp_base.splay_ok hz0_safe harena_nb hsafe hi.sf
      ht_perm hx_in hhp_sp ω with
    ⟨st', c_sp, t', hrun_sp, hsf', hsafe', hr_root, ht_perm', hev', hsteps', hrev', hht',
      hpp', hout', hstat', hfr', hphi_all⟩
  rcases LctExposeInvs.of_splay hi ht_perm ht_free hsf' hev' hsteps' ht_perm'
      (hr_root ▸ hpp') hout' hstat' hfr' with
    ⟨hi', hpar_eq, hrep_eq, hvs_fn, hheavy_eq⟩
  have hphi_le : c_sp + (st'.mem (nb - 1) - mem (nb - 1)) + lctPhi L st'.mem b n ≤
      lctPhi L mem b n + 3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) + C_SPLAY_CONST L := by
    have hlog_t : t.rank (lctVSize mem nb cap) ≤ Nat.log 2 (n + 2) + 1 :=
      treeRank_le_log_of_invs hi.sf hi.subdivOk.1 hi.auxPathOk ht_mem
    have hmul_rk : 3 * K_SPLAY_STEP L * t.rank (lctVSize mem nb cap) ≤
        3 * K_SPLAY_STEP L * (Nat.log 2 (n + 2) + 1) :=
      Nat.mul_le_mul_left _ hlog_t
    have hvs_eq : lctVSize st'.mem nb cap = lctVSize mem nb cap := funext hvs_fn
    have hsp := (hphi_all (lctVSize mem nb cap)).2
    nth_rw 1 [← hvs_eq] at hsp
    unfold lctPhi
    rw [hheavy_eq] at *
    dsimp only [nb, cap] at hsp hmul_rk ⊢
    omega
  exact ⟨st', c_sp, t', hrun_sp, hi', hsafe', hr_root, ht_perm', hev', hsteps', hrev', hht',
    hpp', hout', hfr', hpar_eq, hrep_eq, hphi_le⟩

/-- Weakens `SafeMem` from `(mem_pre[nb - 1 := hp_eff], hp_eff)` back to `(mem₀[nb - 1 := hp_caller],
hp_caller)` when `mem_pre` agrees with `mem₀` outside `[hp_caller, hp_eff)`. -/
theorem link_safeMem_weaken {b nb cap hp_caller hp_eff : ℕ} {mem₀ mem_pre mem_st : ℕ → ℕ}
    (hnb : nb = lctNodesBase b)
    (hle : hp_caller ≤ hp_eff)
    (harena_hp : lctArenaHi b cap ≤ hp_caller)
    (hpre_out : ∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_pre a = mem₀ a)
    (hsafe : SafeMem (Function.update mem_pre (nb - 1) hp_eff) nb cap hp_eff mem_st) :
    SafeMem (Function.update mem₀ (nb - 1) hp_caller) nb cap hp_caller mem_st := by
  have hpos : 1 ≤ nb := by rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE; omega
  have hlt_arena : nb - 1 < nb + NODE_STRIDE * (cap + 1) := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    unfold NODE_STRIDE at hmul
    omega
  have hnb1_lt_hp : nb - 1 < hp_caller := by
    have : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := by
      simpa [lctArenaHi, hnb] using harena_hp
    omega
  refine ⟨le_trans hle hsafe.1, ?_, hsafe.2.2.1, ?_⟩
  · intro a ha
    have ha_ne : a ≠ nb - 1 := by
      rcases ha with hl | ⟨hl, _⟩ | ⟨hl, _⟩
      · omega
      · omega
      · exact ne_of_gt (lt_of_lt_of_le hlt_arena hl)
    have ha' : a < nb - 1 ∨ (nb ≤ a ∧ a < nb + NODE_STRIDE) ∨
        (nb + NODE_STRIDE * (cap + 1) ≤ a ∧ a < hp_eff) := by
      rcases ha with hl | hl | ⟨hl, hr⟩
      · exact Or.inl hl
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr ⟨hl, lt_of_lt_of_le hr hle⟩)
    rw [hsafe.2.1 a ha', Function.update_of_ne ha_ne, Function.update_of_ne ha_ne]
    rcases ha with hl | ⟨_, hr⟩ | ⟨_, hr⟩
    · exact hpre_out a (Or.inl (lt_trans hl hnb1_lt_hp))
    · have hle_arena : nb + NODE_STRIDE ≤ nb + NODE_STRIDE * (cap + 1) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right NODE_STRIDE (Nat.succ_pos cap)) nb
      have harena_le : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := by
        simpa [lctArenaHi, hnb] using harena_hp
      exact hpre_out a (Or.inl (lt_of_lt_of_le hr (le_trans hle_arena harena_le)))
    · exact hpre_out a (Or.inl hr)
  · intro x off hx1 hx2 hoff
    rcases hsafe.2.2.2 x off hx1 hx2 hoff with hp0 | hp_hi | ⟨y, off', hy1, hy2, hoff', hy_eq⟩
    · exact Or.inl hp0
    · exact Or.inr (Or.inl (le_trans hle hp_hi))
    · refine Or.inr (Or.inr ⟨y, off', hy1, hy2, hoff', ?_⟩)
      have hy_addr : nb + NODE_STRIDE * y + off' < nb + NODE_STRIDE * (cap + 1) := by
        have : off' < NODE_STRIDE := ptrOffs_lt_stride hoff'
        have : NODE_STRIDE * y + off' < NODE_STRIDE * (cap + 1) := by
          have := Nat.mul_le_mul_left NODE_STRIDE (by omega : y + 1 ≤ cap + 1)
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
        omega
      have hle_y : nb ≤ nb + NODE_STRIDE * y + off' :=
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      have hne_y : nb + NODE_STRIDE * y + off' ≠ nb - 1 := by omega
      have hlt_hp_y : nb + NODE_STRIDE * y + off' < hp_caller :=
        lt_of_lt_of_le hy_addr (by simpa [lctArenaHi, hnb] using harena_hp)
      rw [hy_eq]
      dsimp only [nodeField]
      rw [Function.update_of_ne hne_y, Function.update_of_ne hne_y, hpre_out _ (Or.inl hlt_hp_y)]

end SharedSplayAndWeaken

section LinkPreShape

private lemma link_re_room1_arith {hp_eff phi0 cr ce n7000 p2w : ℕ}
    (h : hp_eff + phi0 + (cr + ce) + n7000 + 1 < p2w) :
    hp_eff + phi0 + cr + n7000 < p2w ∧ hp_eff < p2w := by
  omega

private lemma link_re_room2_arith {c_re s1 hp_eff phi0 phi1 cr ce n7000 p2w : ℕ}
    (hle1 : hp_eff ≤ s1)
    (h1 : c_re + (s1 - hp_eff) + phi1 ≤ phi0 + cr)
    (h2 : hp_eff + phi0 + (cr + ce) + n7000 + 1 < p2w) :
    s1 + phi1 + ce + n7000 < p2w := by
  omega

private lemma link_re_phi_arith {c_re c_exp s1 s2 hp_eff phi0 phi1 phi2 cr ce : ℕ}
    (h1 : c_re + (s1 - hp_eff) + phi1 ≤ phi0 + cr)
    (h2 : c_exp + (s2 - s1) + phi2 ≤ phi1 + ce)
    (hle1 : hp_eff ≤ s1) (hle2 : s1 ≤ s2) :
    c_re + c_exp + (s2 - hp_eff) + phi2 ≤ phi0 + (cr + ce) := by
  omega

private lemma link_exit_lt_arith {c_re c_exp s2 hp_eff phi0 phi2 cr_ce n7000 p2w : ℕ}
    (hle : hp_eff ≤ s2)
    (h1 : c_re + c_exp + (s2 - hp_eff) + phi2 ≤ phi0 + cr_ce)
    (h2 : hp_eff + phi0 + cr_ce + n7000 + 1 < p2w) :
    s2 + 1 < p2w := by
  omega

/-- Runs `lctRerootBody` at `u + 1` and `exposeBody` at `v + 1` after pre-allocation, returning
both `LctExposeInvs` and `lctAuxParent st₂.mem nb cap (u + 1) = 0`. -/
theorem rerootExpose_link_runs {w h L P b u v hp_caller hp_eff pos : ℕ}
    {F : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem_pre : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hrep_pre : LctMemRep w h L P b F x₀ mem_pre)
    (hu : u < F.n) (hv : v < F.n)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_eff)
    (hz_eff : ZeroFrom mem_pre hp_eff)
    (hhp_le : hp_caller ≤ hp_eff)
    (hroom : hp_eff + lctPhi L mem_pre b F.n +
      (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w)
    (ω : ℕ → Bool) :
    let nb := lctNodesBase b
    let cap := lctCap F.n
    let mem₁ := Function.update mem_pre (nb - 1) hp_eff
    ∃ st₁ st₂ c_re c_exp l_v rest_v x₂,
      Runs w p ω (lctRerootBody lp) (startState [nb, u + 1] mem₁ pos) (.returned 0) st₁ c_re ∧
      Runs w p ω (exposeBody lp.splay) (startState [nb, v + 1] st₁.mem st₁.pos)
        (.returned (v + 1)) st₂ c_exp ∧
      LctExposeInvs w h L P b F.n x₀.freeEdges x₀.edgeMap
        (AuxTree.node (v + 1) l_v .leaf :: rest_v) st₂.mem ∧
      SafeMem mem₁ nb cap hp_eff st₂.mem ∧
      ZeroFrom st₂.mem (st₂.mem (nb - 1)) ∧
      hp_eff ≤ st₂.mem (nb - 1) ∧
      nodeField st₂.mem nb (v + 1) OFF_PPAR = 0 ∧
      lctAuxParent st₂.mem nb cap (u + 1) = 0 ∧
      (AuxTree.node (v + 1) l_v .leaf).evalInorder (revFlag st₂.mem nb) false =
        l_v.evalInorder (revFlag st₂.mem nb) false ++ [v + 1] ∧
      ((AuxTree.node (v + 1) l_v .leaf).evalInorder (revFlag st₂.mem nb) false).getLast? =
        some (v + 1) ∧
      c_re + c_exp + (st₂.mem (nb - 1) - hp_eff) + lctPhi L st₂.mem b F.n ≤
        lctPhi L mem_pre b F.n + (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) ∧
      LctMemRep w h L P b F x₂ st₂.mem ∧
      x₂.trees = AuxTree.node (v + 1) l_v .leaf :: rest_v ∧
      SlotZeroOk mem₁ nb ∧
      PtrFootOk b mem₁ x₀ L ∧
      (∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_caller → mem₁ a = mem_pre a) ∧
      hp_eff < 2 ^ w ∧
      RootMove (lctAuxParent mem_pre nb cap) (lctAuxParent st₂.mem nb cap) cap (u + 1) := by
  intro nb cap mem₁
  have hroom' : hp_eff + lctPhi L mem_pre b F.n +
      (C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1)) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w := by
    rw [← Nat.add_mul]; exact hroom
  have hrm1 := link_re_room1_arith hroom'
  have hhpeff_w : hp_eff < 2 ^ w := hrm1.2
  rcases enterOp_invs hrep_pre hfoot hz_eff le_rfl hhpeff_w with
    ⟨hi₁, hsafe₁, hphi_eq₁, hz₁, hslot0₁, hpf₁, _hpar₁, hag₁⟩
  have hmem1_hp : mem₁ (nb - 1) = hp_eff := Function.update_self _ _ _
  have harena_safe : lctArenaHi b cap ≤ hp_eff := by
    have := hrep_pre.hp_le_of_foot hfoot
    exact le_trans this.1 this.2.1
  have hedge_lt : ∀ q ∈ x₀.edgeMap, q.2.u < F.n ∧ q.2.v < F.n := fun q hq => by
    have he := hrep_pre.valid.1 q.2 (hrep_pre.edgeMap_snd_perm.mem_iff.1 (List.mem_map.2 ⟨q, hq, rfl⟩))
    exact ⟨he.1, he.2.1⟩
  have hslot_cov : ∀ z, F.n + 1 ≤ z → z ≤ cap →
      z ∈ x₀.freeEdges ∨ ∃ q ∈ x₀.edgeMap, q.1 = z := fun z hz1 hz2 => by
    have hzm : z ∈ (List.range F.n).map (F.n + 1 + ·) := by
      refine List.mem_map.2 ⟨z - (F.n + 1), List.mem_range.2 ?_, ?_⟩
      · dsimp only [cap, lctCap] at hz2; omega
      · omega
    rcases List.mem_append.1 (hrep_pre.slots_perm.symm.mem_iff.1 hzm) with he | hf
    · rcases List.mem_map.1 he with ⟨q, hq, hqe⟩
      exact Or.inr ⟨q, hq, hqe⟩
    · exact Or.inl hf
  have hroom_re : mem₁ (nb - 1) + lctPhi L mem₁ b F.n +
      C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) < 2 ^ w := by
    rw [hmem1_hp, hphi_eq₁]
    exact hrm1.1
  rcases lctRerootBody_runs (pos := pos) p lp mem₁ mem₁ hp_base hp_sp hexpose_eq hslot0₁
      harena_safe hsafe₁ hi₁ hu (by change ZeroFrom mem₁ (mem₁ (nb - 1)); rw [hmem1_hp]; exact hz₁)
      hedge_lt hslot_cov hroom_re ω with
    ⟨st₁, c_re, _l₁, _rest₁, hrun_re, hi_re, hsafe_re, hfr_re, _hpp1, hpar1_zero,
      _hreach, hmove_re, hphi_re⟩
  have hz_re : ZeroFrom st₁.mem (st₁.mem (nb - 1)) := hfr_re.2.2.2.2.1
  have hle_re : hp_eff ≤ st₁.mem (nb - 1) := by
    rw [← hmem1_hp]
    exact hfr_re.2.2.1
  have hphi_re' : c_re + (st₁.mem (nb - 1) - hp_eff) + lctPhi L st₁.mem b F.n ≤
      lctPhi L mem_pre b F.n + C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) := by
    rw [hmem1_hp, hphi_eq₁] at hphi_re
    exact hphi_re
  have hroom_exp : st₁.mem (nb - 1) + lctPhi L st₁.mem b F.n +
      C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) < 2 ^ w :=
    link_re_room2_arith hle_re hphi_re' hroom'
  rcases hp_sp with ⟨spB, hspB⟩
  have hsp_ok := hp_base.splay_ok
  have hsp_has := hp_base.splay_hasAt
  rcases exposeBody_runs (pos := st₁.pos) p lp.splay mem₁ st₁.mem hsp_has ⟨spB, hspB⟩ hsp_ok
      hslot0₁ harena_safe hsafe_re hi_re hv hz_re hroom_exp ω with
    ⟨st₂, c_exp, l_v, rest_v, hrun_exp, hi₂, hsafe₂, hfr₂, hpar2_eq, hpp₂, _hrev₂, _hht₂, hev₂,
      hphi_exp⟩
  have hz₂ : ZeroFrom st₂.mem (st₂.mem (nb - 1)) := hfr₂.2.2.2.2.1
  have hle_exp : st₁.mem (nb - 1) ≤ st₂.mem (nb - 1) := hfr₂.2.2.1
  have hpar2_u : lctAuxParent st₂.mem nb cap (u + 1) = 0 := by
    rw [hpar2_eq (u + 1)]
    exact hpar1_zero
  have hlast_v :
      ((AuxTree.node (v + 1) l_v .leaf).evalInorder (revFlag st₂.mem nb) false).getLast? =
        some (v + 1) := by
    rw [hev₂, List.getLast?_concat]
  have hcost_tot : c_re + c_exp + (st₂.mem (nb - 1) - hp_eff) + lctPhi L st₂.mem b F.n ≤
      lctPhi L mem_pre b F.n + (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) := by
    rw [Nat.add_mul]
    exact link_re_phi_arith hphi_re' hphi_exp hle_re hle_exp
  have hle₂ : hp_eff ≤ st₂.mem (nb - 1) := le_trans hle_re hle_exp
  have hfin_lt : st₂.mem (nb - 1) + 1 < 2 ^ w :=
    link_exit_lt_arith hle₂ hcost_tot hroom
  have hx₂_pre : ∃ x₂ : LctConc, LctMemRep w h L P b F x₂ st₂.mem ∧
      x₂.trees = AuxTree.node (v + 1) l_v .leaf :: rest_v := by
    let x_tmp : LctConc :=
      { n := F.n
        trees := AuxTree.node (v + 1) l_v .leaf :: rest_v
        freeEdges := x₀.freeEdges
        edgeMap := x₀.edgeMap
        regions := x₀.regions ++ [(hp_eff, st₂.mem (nb - 1) + 1)]
        hpHi := st₂.mem (nb - 1) + 1 }
    refine ⟨x_tmp, ?_, rfl⟩
    rcases exitOp_rep (space := st₂.mem (nb - 1) + 1) hrep_pre hfoot le_rfl rfl hrep_pre.valid
        hrep_pre.edgeFits hslot0₁ hpf₁ (fun a ha => hag₁ a ha) hsafe₂ hi₂.sf hi₂.hdrN hi₂.hdrCap
        hi₂.hdrL hi₂.hdrP hrep_pre.edgeMap_snd_perm hrep_pre.slots_perm hi₂.freeChain
        hi₂.freeNodeOk hi₂.vertexOk hi₂.edgeOk hi₂.auxPathOk hi₂.subdivOk hfin_lt
        (Nat.le_add_left _ _) (fun _ _ => rfl) with
      ⟨hrep₂, _, _⟩
    exact hrep₂
  rcases hx₂_pre with ⟨x₂, hrep₂, hx₂_trees⟩
  refine ⟨st₁, st₂, c_re, c_exp, l_v, rest_v, x₂, hrun_re, hrun_exp, hi₂, hsafe₂, hz₂,
    hle₂, hpp₂, hpar2_u, hev₂, hlast_v, hcost_tot, hrep₂, hx₂_trees, hslot0₁, hpf₁, ?_, hhpeff_w,
    ?_⟩
  · intro a ha
    apply hag₁ a
    rcases ha with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, lt_of_lt_of_le h2 hhp_le⟩
  · have hpar1 : ∀ z, lctAuxParent mem_pre nb cap z = lctAuxParent mem₁ nb cap z :=
      lctAuxParent_agree (fun i hi _ => by
        have h3 : 3 ≤ nb := lctNodesBase_ge3 b
        dsimp only [mem₁]
        rw [Function.update_of_ne (by omega)])
    have hm := rootMove_of_agree hmove_re hpar2_eq
    exact (funext hpar1) ▸ hm

private lemma rootAbove_of_par_zero (par : ℕ → ℕ) {c x : ℕ} (hc : 1 ≤ c) (hp : par x = 0) :
    rootAbove par c x = x := by
  have hc' : c = (c - 1) + 1 := (Nat.sub_add_cancel hc).symm
  rw [hc']
  simp [rootAbove, hp]

/-- When `¬ F.SameComp u v`, `reroot u` followed by `expose v` puts `u + 1` strictly outside
`t_v = .node (v + 1) l_v .leaf`. -/
theorem link_not_sameComp_disjoint {w h L P b u v : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {l_v : AuxTree} {rest_v : List AuxTree}
    (hi : LctExposeInvs w h L P b F.n freeEdges edgeMap
      (AuxTree.node (v + 1) l_v .leaf :: rest_v) mem)
    (hrep : LctMemRep w h L P b F x mem)
    (hu : u < F.n) (hv : v < F.n) (hdisc : ¬ F.SameComp u v)
    (hpar_u : lctAuxParent mem (lctNodesBase b) (lctCap F.n) (u + 1) = 0)
    (hlast_v :
      ((AuxTree.node (v + 1) l_v .leaf).evalInorder (revFlag mem (lctNodesBase b)) false).getLast? =
        some (v + 1)) :
    u + 1 ∉ (AuxTree.node (v + 1) l_v .leaf).toList := by
  intro hu_in
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let t_v := AuxTree.node (v + 1) l_v .leaf
  let par := lctAuxParent mem nb cap
  have htree_seq : lctTreeSeq mem nb cap t_v.rootId = t_v.evalInorder (revFlag mem nb) false :=
    hi.sf.lctTreeSeq_eq (t := t_v) (by simp [t_v])
  let seq := lctTreeSeq mem nb cap t_v.rootId
  have hu_seq : u + 1 ∈ seq := by
    rw [show seq = t_v.evalInorder (revFlag mem nb) false from htree_seq]
    exact (t_v.evalInorder_perm (revFlag mem nb) false).symm.mem_iff.1 hu_in
  rcases List.getElem_of_mem hu_seq with ⟨idx, hidx, hidx_eq⟩
  have htv_tok := (hi.sf.trees_ok t_v (by simp [t_v])).2.2
  have hcap_pos : 1 ≤ cap := by unfold cap lctCap; omega
  have hidx_zero : idx = 0 := by
    cases idx with
    | zero => rfl
    | succ j =>
        have hp := lctAuxParent_of_tree hi.sf hi.ppar_le_cap (t := t_v) (by simp [t_v]) (j + 1) hidx
        have hlt_j : j < seq.length := by omega
        have hget_j : seq[j]! = seq[j] := by
          simp [getElem!_def, List.getElem?_eq_getElem hlt_j]
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hp
        change par seq[j + 1] = seq[j]! at hp
        rw [hidx_eq, hget_j] at hp
        have hseq_j_mem : seq[j] ∈ t_v.toList := by
          have : seq[j] ∈ t_v.evalInorder (revFlag mem nb) false := by
            rw [← htree_seq]; exact List.getElem_mem hlt_j
          exact (t_v.evalInorder_perm (revFlag mem nb) false).mem_iff.1 this
        have hj_bd := htv_tok.nodup_perm_mem hseq_j_mem
        have : 0 = seq[j] := hpar_u.symm.trans hp
        omega
  have hseq0 : seq[0]'(by omega) = u + 1 := by simpa [hidx_zero] using hidx_eq
  have hrb_u : rootAbove par cap (u + 1) = u + 1 :=
    rootAbove_of_par_zero par hcap_pos hpar_u
  have hp0 : par 0 = 0 := lctAuxParent_zero mem nb cap
  have hle_par : ∀ z, 1 ≤ z → z ≤ cap → par z ≤ cap := fun z _ _ =>
    lctAuxParent_le_cap mem nb cap z
  have hwalk : ∀ k (hk : k < seq.length), rootAbove par cap seq[k] = u + 1 := by
    intro k hk
    induction k with
    | zero => rw [hseq0]; exact hrb_u
    | succ k ih =>
        have hk_lt : k < seq.length := by omega
        have hmem_k1 : seq[k + 1] ∈ t_v.toList := by
          have : seq[k + 1] ∈ t_v.evalInorder (revFlag mem nb) false := by
            rw [← htree_seq]; exact List.getElem_mem hk
          exact (t_v.evalInorder_perm (revFlag mem nb) false).mem_iff.1 this
        have hmem_k : seq[k] ∈ t_v.toList := by
          have : seq[k] ∈ t_v.evalInorder (revFlag mem nb) false := by
            rw [← htree_seq]; exact List.getElem_mem hk_lt
          exact (t_v.evalInorder_perm (revFlag mem nb) false).mem_iff.1 this
        have hk1_bd := htv_tok.nodup_perm_mem hmem_k1
        have hk_bd := htv_tok.nodup_perm_mem hmem_k
        have hp_k1 := lctAuxParent_of_tree hi.sf hi.ppar_le_cap (t := t_v) (by simp [t_v]) (k + 1) hk
        have hget_k : seq[k]! = seq[k] := by
          simp [getElem!_def, List.getElem?_eq_getElem hk_lt]
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hp_k1
        have hpar_k1 : par seq[k + 1] = seq[k] := by
          change par seq[k + 1] = seq[k]! at hp_k1
          rw [hp_k1, hget_k]
        have hne0 : par seq[k + 1] ≠ 0 := by rw [hpar_k1]; omega
        have hstep := rootAbove_step hp0 hle_par hi.subdivOk.1 hk1_bd.1 hk1_bd.2 hne0
        rw [← hstep, hpar_k1]
        exact ih hk_lt
  have hne_nil : seq ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlast_seq : seq.getLast? = some (v + 1) := by
    rw [show seq = t_v.evalInorder (revFlag mem nb) false from htree_seq]
    exact hlast_v
  have hlast_idx : seq[seq.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hne_nil) (by omega)) =
      v + 1 := by
    have hg : seq.getLast hne_nil = v + 1 := by
      have hgl := List.getLast?_eq_some_getLast hne_nil
      rw [hlast_seq] at hgl
      exact Option.some.inj hgl.symm
    exact (List.getLast_eq_getElem hne_nil).symm.trans hg
  have hrb_v : rootAbove par cap (v + 1) = u + 1 := by
    rw [← hlast_idx]
    exact hwalk (seq.length - 1) (Nat.sub_lt (List.length_pos_of_ne_nil hne_nil) (by omega))
  exact hdisc ((hrep.sameComp_iff_rootAbove hu hv).2 (hrb_u.trans hrb_v.symm))

/-- Finding `t_u ∈ rest_v` containing `u + 1` and putting it at the head of a permutation of
`t_v :: rest_v`. -/
theorem link_find_u_tree {w h L P b n u : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {t_v : AuxTree} {rest_v : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (t_v :: rest_v) mem)
    (hu : u < n) (hnot_tv : u + 1 ∉ t_v.toList) :
    ∃ t_u rest_other,
      rest_v.Perm (t_u :: rest_other) ∧
      (t_v :: rest_v).Perm (t_u :: t_v :: rest_other) ∧
      u + 1 ∈ t_u.toList ∧
      t_u.rootId ∉ freeEdges := by
  have hcap_range : u + 1 ∈ (List.range (lctCap n)).map (· + 1) :=
    List.mem_map.2 ⟨u, List.mem_range.2 (by unfold lctCap; omega), rfl⟩
  have hu_flat := hi.sf.perm.symm.mem_iff.1 hcap_range
  rw [List.flatMap_cons, List.mem_append, List.mem_flatMap] at hu_flat
  rcases hu_flat with h_in_tv | ⟨t_u, ht_u_mem, hu_in_tu⟩
  · exact absurd h_in_tv hnot_tv
  · classical
    refine ⟨t_u, rest_v.erase t_u, List.perm_cons_erase ht_u_mem, ?_, hu_in_tu, ?_⟩
    · exact (List.Perm.cons t_v (List.perm_cons_erase ht_u_mem)).trans (List.Perm.swap t_u t_v _)
    · intro hfree
      have hnd_all := hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
      set tid := t_u.rootId
      rcases hi.freeNodeOk tid hfree with ⟨hge, _, htr, _⟩
      have htu_in_all : t_u ∈ t_v :: rest_v := List.mem_cons_of_mem _ ht_u_mem
      have htu_ne : t_u ≠ .leaf := (hi.sf.trees_ok t_u htu_in_all).1
      have hsame := unique_tree_of_mem hnd_all htu_in_all htr (AuxTree.rootId_mem_toList htu_ne)
        (by simp [AuxTree.toList]; rfl)
      rw [hsame] at hu_in_tu
      have hu_eq_tid : u + 1 = tid := by
        simp only [AuxTree.toList, List.nil_append, List.append_nil, List.mem_singleton] at hu_in_tu
        exact hu_in_tu
      omega

end LinkPreShape
end MinCostFlow.LinkCut.Prog
end
