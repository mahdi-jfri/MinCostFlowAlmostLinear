module

public import MinCostFlow.LinkCut.Prog.MathForestCutMain

/-!
# Word-RAM `cut` Procedure Correctness

Proves `lctCutBody_runs`: running `lctCutBody lp` on a represented forest `F` with any two
numbers `x, y` ends with a representation of `F.cut x y`, respects the heap discipline, and
pays amortized cost at most `C_CUT_OP L * (log (n + 2) + 1)`.

The program first stores the heap pointer in the header. If `x` or `y` is not a vertex, it
does nothing more, and `F.cut x y = F` (`cut_eq_self_of_bad_args`). Otherwise it runs the main
branch (`lctCutMainBody_runs`). In both cases it returns the heap pointer plus one.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutRoots

/-- How `cut x y` moves the represented roots. When `x` or `y` is not a vertex, nothing moves.
Otherwise the tree of `x` first gets root `x` (the reroot). If an edge `{x, y}` is removed, the
part of `y` gets root `y`, the part of `x` gets root `x`, and other trees keep their roots. -/
def CutRoots (mem₀ mem' : ℕ → ℕ) (b : ℕ) (F : MathForest) (x y : ℕ) : Prop :=
  ∀ z < F.n,
    (¬ (x < F.n ∧ y < F.n) → lctCanonRoot mem' b F.n z = lctCanonRoot mem₀ b F.n z) ∧
    (x < F.n → y < F.n → F.cut x y = F →
      lctCanonRoot mem' b F.n z =
        if lctCanonRoot mem₀ b F.n z = lctCanonRoot mem₀ b F.n x then x
        else lctCanonRoot mem₀ b F.n z) ∧
    (x < F.n → y < F.n → F.cut x y ≠ F →
      ((F.cut x y).SameComp z y → lctCanonRoot mem' b F.n z = y) ∧
      (¬ (F.cut x y).SameComp z y → (F.cut x y).SameComp z x → lctCanonRoot mem' b F.n z = x) ∧
      (¬ (F.cut x y).SameComp z y → ¬ (F.cut x y).SameComp z x →
        lctCanonRoot mem' b F.n z = lctCanonRoot mem₀ b F.n z))

/-- The parent-map facts of the run of `cut` give `CutRoots`. -/
theorem cut_canonRoot {w h L P b x y : ℕ} {F : MathForest} {x₀ x' : LctConc}
    {mem₀ mem' : ℕ → ℕ}
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hrep' : LctMemRep w h L P b (F.cut x y) x' mem')
    (hgood : x < F.n ∧ y < F.n → ∃ par₂,
      RootMove (lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n)) par₂ (lctCap F.n) (x + 1) ∧
      CutParShape par₂ (lctAuxParent mem' (lctNodesBase b) (lctCap F.n)) F x y)
    (hbad : ¬ (x < F.n ∧ y < F.n) → ∀ q, lctAuxParent mem' (lctNodesBase b) (lctCap F.n) q =
      lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n) q) :
    CutRoots mem₀ mem' b F x y := by
  intro z hz
  set nb := lctNodesBase b
  set cap := lctCap F.n
  have hFn : (F.cut x y).n = F.n := rfl
  have hcap : ∀ q < F.n, q + 1 ≤ cap := fun q hq => by simp only [cap, lctCap]; omega
  have hdef : ∀ (mem : ℕ → ℕ) q, lctCanonRoot mem b F.n q =
      rootAbove (lctAuxParent mem nb cap) cap (q + 1) - 1 := fun _ _ => rfl
  have hR₀ : ∀ q < F.n, rootAbove (lctAuxParent mem₀ nb cap) cap (q + 1) =
      lctCanonRoot mem₀ b F.n q + 1 := fun q hq => (hrep₀.lctCanonRoot_spec hq).2.1.symm
  have hR' : ∀ q < F.n, rootAbove (lctAuxParent mem' nb cap) cap (q + 1) =
      lctCanonRoot mem' b F.n q + 1 := fun q hq => (hrep'.lctCanonRoot_spec (by rw [hFn]; exact hq)).2.1.symm
  refine ⟨fun hb => ?_, fun hx hy hcut => ?_, fun hx hy hcut => ?_⟩
  · rw [hdef, hdef mem₀, funext (hbad hb)]
  · obtain ⟨par₂, hmove, hshape⟩ := hgood ⟨hx, hy⟩
    rcases hshape with ⟨hpar, _⟩ | ⟨hne, _⟩
    · have h2 := hmove (z + 1) (by omega) (hcap z hz)
      rw [hdef, funext hpar, h2, hR₀ z hz, hR₀ x hx]
      split_ifs <;> omega
    · exact absurd hcut hne
  · obtain ⟨par₂, hmove, hshape⟩ := hgood ⟨hx, hy⟩
    rcases hshape with ⟨_, hcut'⟩ | ⟨_, ed, hed, hpar⟩
    · exact absurd hcut' hcut
    have hcap1 : 1 ≤ cap := le_trans (by omega) (hcap x hx)
    have hpx : lctAuxParent mem' nb cap (x + 1) = 0 := by rw [hpar]; simp
    have hpy : lctAuxParent mem' nb cap (y + 1) = 0 := by rw [hpar]; simp
    have hcx : lctCanonRoot mem' b F.n x = x := by
      rw [hdef, rootAbove_self_of_par_zero hcap1 hpx]; omega
    have hcy : lctCanonRoot mem' b F.n y = y := by
      rw [hdef, rootAbove_self_of_par_zero hcap1 hpy]; omega
    have hsc : ∀ q, q < F.n → (lctCanonRoot mem' b F.n z = lctCanonRoot mem' b F.n q ↔
        (F.cut x y).SameComp z q) := fun q hq =>
      ((hrep'.lctCanonRoot_spec (v := q) (by rw [hFn]; exact hq)).2.2.2 z (by rw [hFn]; exact hz))
    refine ⟨fun hzy => ?_, fun _ hzx => ?_, fun hny hnx => ?_⟩
    · rw [(hsc y hy).2 hzy, hcy]
    · rw [(hsc x hx).2 hzx, hcx]
    · have hlt : lctCanonRoot mem' b F.n z < F.n :=
        (hrep'.lctCanonRoot_spec (by rw [hFn]; exact hz)).1
      have hnx' : lctCanonRoot mem' b F.n z ≠ x := fun h => hnx ((hsc x hx).1 (h.trans hcx.symm))
      have hny' : lctCanonRoot mem' b F.n z ≠ y := fun h => hny ((hsc y hy).1 (h.trans hcy.symm))
      have hdich := rootAbove_zeroed (par := par₂) (par' := lctAuxParent mem' nb cap)
        (S := fun q => q = ed ∨ q = x + 1 ∨ q = y + 1)
        (fun q hq => by rw [hpar q]; simp only [hq, ↓reduceIte])
        (fun q hq => by rw [hpar q]; simp only [hq, ↓reduceIte]) cap (z + 1)
      rw [hR' z hz] at hdich
      rcases hdich with h | h
      · omega
      · have h2 := hmove (z + 1) (by omega) (hcap z hz)
        rw [hR₀ z hz, hR₀ x hx, ← h] at h2
        split_ifs at h2 <;> omega

end CutRoots

section CutTop

private lemma cut_top_budget {c_mid s hp phi0 phi_e B : ℕ}
    (h : c_mid + 40 + (s - hp) + phi_e ≤ phi0 + B) (hle : hp ≤ s) :
    5 + (5 + (c_mid + (5 + 4 + 1) + 1) + 1) + 1 + (s + 1 - hp) + phi_e ≤ phi0 + B := by
  omega

private lemma cut_top_room {c_mid s hp phi0 phi_e B m p2w space : ℕ}
    (h : c_mid + 40 + (s - hp) + phi_e ≤ phi0 + B) (hle : hp ≤ s)
    (hroom : hp + phi0 + B + m + 1 < p2w) (hspace : phi0 + B + 1 ≤ space) :
    s + 1 < p2w ∧ s + 1 ≤ hp + space := by
  omega

/-- Correctness and amortized cost of `lctCutBody`, on `args = [b, x, y, hp_caller]`. -/
theorem lctCutBody_runs {w h L P b x y hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hroom : hp_caller + lctPhi L mem₀ b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w)
    (hspace : lctPhi L mem₀ b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) + 1 ≤ space)
    (ω : ℕ → Bool) :
    ∃ hp_final st' c x',
      Runs w p ω (lctCutBody lp) (startState [b, x, y, hp_caller] mem₀ pos)
        (.returned hp_final) st' c ∧
      LctMemRep w h L P b (F.cut x y) x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      c + (hp_final - hp_caller) + lctPhi L st'.mem b (F.cut x y).n ≤
        lctPhi L mem₀ b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      CutRoots mem₀ st'.mem b F x y := by
  have hbh_eq : b + LCT_HDR_HP = lctNodesBase b - 1 := by
    unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
  have hrep₀_hp := hrep₀.hp_le_of_foot hfoot
  have harena_le : lctArenaHi b (lctCap F.n) ≤ hp_caller := le_trans hrep₀_hp.1 hrep₀_hp.2.1
  have hhp_w : hp_caller < 2 ^ w := by omega
  have hC : 400000 ≤ C_CUT_OP L := by unfold C_CUT_OP; omega
  obtain ⟨hi0, hsafe0, hphi0_eq, _, hz0_safe, hpf0, _, hag0⟩ :=
    enterOp_invs hrep₀ hfoot hz₀ le_rfl hhp_w
  set mem₁ := Function.update mem₀ (lctNodesBase b - 1) hp_caller with hmem₁
  have hN_ne : b + LCT_HDR_N ≠ lctNodesBase b - 1 := by
    unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_N; omega
  have hmemN : mem₀ (b + LCT_HDR_N) = F.n := by
    have := hi0.hdrN
    rwa [hmem₁, Function.update_of_ne hN_ne] at this
  have harena_def : lctArenaHi b (lctCap F.n) = lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1) :=
    rfl
  have hnb_w : b + LCT_HDR_HP < 2 ^ w := by
    unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP at *; omega
  have hNw : b + LCT_HDR_N < 2 ^ w := by
    unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_N at *; omega
  have h1w : 1 < 2 ^ w := by omega
  -- The first two statements.
  let regs0 : ℕ → ℕ := fun i => [b, x, y, hp_caller].getD i 0
  let regs4 := Function.update regs0 4 F.n
  have hs4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const LCT_HDR_N))))
      (startState [b, x, y, hp_caller] mem₀ pos) .normal
      { mem := mem₀, regs := regs4, pos := pos } 5 :=
    runs_assign_iff.2 ⟨F.n, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_const (by unfold LCT_HDR_N; omega)) hNw) hmemN, rfl, rfl, rfl⟩
  have hsHP : Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 3))
      { mem := mem₀, regs := regs4, pos := pos } .normal
      { mem := mem₁, regs := regs4, pos := pos } 5 :=
    runs_store_iff.2 ⟨b + LCT_HDR_HP, hp_caller, Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_const (by unfold LCT_HDR_HP at hnb_w ⊢; omega)) hnb_w, Expr.eval_reg_of_eq rfl, rfl,
      by rw [hbh_eq], rfl⟩
  have hr0 : regs4 0 = b := rfl
  have hr1 : regs4 1 = x := rfl
  have hr2 : regs4 2 = y := rfl
  have hr4 : regs4 4 = F.n := rfl
  let st_pre : State := { mem := mem₁, regs := regs4, pos := pos }
  have hgood_eval : Expr.eval w st_pre lctCutGoodExpr =
      some ((if x < F.n then 1 else 0) * (if y < F.n then 1 else 0)) := by
    have hle1 : ∀ (q : Prop) [Decidable q], (if q then 1 else 0) ≤ 1 := fun q _ => by
      split_ifs <;> omega
    have hm := Nat.mul_le_mul (hle1 (x < F.n)) (hle1 (y < F.n))
    exact Expr.eval_mul (Expr.eval_lt_op (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr4) h1w)
      (Expr.eval_lt_op (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr4) h1w) (by omega)
  -- The middle part ends with the invariants of `F.cut x y`.
  have hmid : ∃ st_end c_mid free1 edgeMap1 trees1 mem_safe,
      Runs w p ω (.cond lctCutGoodExpr (lctCutMainBody lp) .nop) st_pre .normal st_end c_mid ∧
      st_end.regs 0 = b ∧
      LctExposeInvs w h L P b F.n free1 edgeMap1 trees1 st_end.mem ∧
      (edgeMap1.map Prod.snd).Perm (F.cut x y).edges ∧
      ((edgeMap1.map Prod.fst) ++ free1).Perm ((List.range F.n).map (F.n + 1 + ·)) ∧
      SafeMem mem_safe (lctNodesBase b) (lctCap F.n) hp_caller st_end.mem ∧
      SlotZeroOk mem_safe (lctNodesBase b) ∧ PtrFootOk b mem_safe x₀ L ∧
      (∀ a, a < b ∨ lctArenaHi b (lctCap F.n) ≤ a ∧ a < hp_caller → mem_safe a = mem₀ a) ∧
      hp_caller ≤ st_end.mem (lctNodesBase b - 1) ∧
      c_mid + 40 + (st_end.mem (lctNodesBase b - 1) - hp_caller) +
        lctPhi L st_end.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      (x < F.n ∧ y < F.n → ∃ par₂,
        RootMove (lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n)) par₂ (lctCap F.n) (x + 1) ∧
        CutParShape par₂ (lctAuxParent st_end.mem (lctNodesBase b) (lctCap F.n)) F x y) ∧
      (¬ (x < F.n ∧ y < F.n) → ∀ q, lctAuxParent st_end.mem (lctNodesBase b) (lctCap F.n) q =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n) q) := by
    by_cases hgood : x < F.n ∧ y < F.n
    · obtain ⟨st_end, c_m, free1, edgeMap1, trees1, mem_safe, hrun_m, hend0, hi_end, hperm1,
          hslots1, hsafe_end, hslot_end, hptr_end, hag_end, hle_end, hbd_m, hpar_m⟩ :=
        lctCutMainBody_runs (pos := pos) p lp mem₀ regs4 hp_base hp_sp hexpose_eq hreroot_eq
          hrep₀ hgood.1 hgood.2 hfoot hz₀ hroom hr0 hr1 hr2 ω
      have hcond : Runs w p ω (.cond lctCutGoodExpr (lctCutMainBody lp) .nop) st_pre .normal
          st_end (lctCutGoodExpr.size + c_m + 1) :=
        runs_cond_iff.2 ⟨1, c_m, by simpa [hgood.1, hgood.2] using hgood_eval,
          by simpa using hrun_m, rfl⟩
      refine ⟨st_end, _, free1, edgeMap1, trees1, mem_safe, hcond, hend0, hi_end, hperm1,
        hslots1, hsafe_end, hslot_end, hptr_end, hag_end, hle_end, ?_, fun _ => hpar_m,
        fun hb => absurd hgood hb⟩
      simp only [lctCutGoodExpr, Expr.size] at hbd_m ⊢
      omega
    · have hcut : F.cut x y = F := by
        apply cut_eq_self_of_bad_args hrep₀.valid
        by_cases hx : x < F.n
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inl (by omega)
      have hzero : (if x < F.n then 1 else 0) * (if y < F.n then 1 else 0) = 0 := by
        by_cases hx : x < F.n
        · have hy : ¬ y < F.n := fun hy => hgood ⟨hx, hy⟩
          simp [hy]
        · simp [hx]
      have hcond : Runs w p ω (.cond lctCutGoodExpr (lctCutMainBody lp) .nop) st_pre .normal
          st_pre (lctCutGoodExpr.size + 1 + 1) :=
        runs_cond_iff.2 ⟨_, 1, hgood_eval,
          by simpa [hzero] using runs_nop_iff.2 ⟨rfl, rfl, rfl⟩, rfl⟩
      have hmem₁_hp : mem₁ (lctNodesBase b - 1) = hp_caller := by simp [mem₁]
      have hlog : 1 ≤ Nat.log 2 (F.n + 2) + 1 := by omega
      have hCl : C_CUT_OP L ≤ C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) :=
        Nat.le_mul_of_pos_right _ hlog
      refine ⟨st_pre, _, x₀.freeEdges, x₀.edgeMap, x₀.trees, mem₁, hcond, hr0, hi0,
        by rw [hcut]; exact hrep₀.edgeMap_snd_perm, hrep₀.slots_perm, hsafe0, hz0_safe, hpf0,
        hag0, by simp only [st_pre, hmem₁_hp, le_refl], ?_, fun hg => absurd hg hgood,
        fun _ q => lctAuxParent_agree (fun i hi _ => by
          have h3 : 3 ≤ lctNodesBase b := lctNodesBase_ge3 b
          show mem₀ i = mem₁ i
          rw [hmem₁, Function.update_of_ne (by omega)]) q⟩
      show _ + 40 + (mem₁ (lctNodesBase b - 1) - hp_caller) + lctPhi L mem₁ b F.n ≤ _
      rw [hmem₁_hp, hphi0_eq]
      simp only [lctCutGoodExpr, Expr.size, Nat.sub_self]
      have h49 : 49 ≤ C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) := le_trans (by omega) hCl
      omega
  obtain ⟨st_end, c_mid, free1, edgeMap1, trees1, mem_safe, hrun_mid, hend0, hi_end, hperm1,
      hslots1, hsafe_end, hslot_end, hptr_end, hag_end, hle_end, hbd_mid, hgood_par,
      hbad_par⟩ := hmid
  -- The last two statements.
  set s_end := st_end.mem (lctNodesBase b - 1) with hs_end
  obtain ⟨hfin_lt, hfin_sp⟩ := cut_top_room hbd_mid hle_end hroom hspace
  have hs13 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 0) (.const LCT_HDR_HP))))
      st_end .normal { st_end with regs := Function.update st_end.regs 13 s_end } 5 :=
    runs_assign_iff.2 ⟨s_end, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hend0)
      (Expr.eval_const (by unfold LCT_HDR_HP at hnb_w ⊢; omega)) hnb_w) (by rw [hbh_eq]), rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 13) (.const 1)))
      { st_end with regs := Function.update st_end.regs 13 s_end } (.returned (s_end + 1))
      { st_end with regs := Function.update st_end.regs 13 s_end } 4 :=
    runs_ret_iff.2 ⟨s_end + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const h1w) hfin_lt, rfl, rfl, rfl⟩
  have hrun := link_runs_seq_normal hs4 (link_runs_seq_normal hsHP
    (link_runs_seq_normal hrun_mid (link_runs_seq_normal hs13 hret)))
  have hexit := exitOp_rep (F0 := F) (F1 := F.cut x y) (x0 := x₀) (mem0 := mem₀)
    (mem_safe := mem_safe) (mem_end := st_end.mem) (mem_fin := st_end.mem)
    (trees1 := trees1) (freeEdges1 := free1) (edgeMap1 := edgeMap1) (space := space)
    hrep₀ hfoot (le_refl hp_caller) rfl (MathForest.cut_valid hrep₀.valid x y)
    (fun e he => hrep₀.edgeFits e (List.mem_of_mem_filter he)) hslot_end hptr_end hag_end
    hsafe_end hi_end.sf hi_end.hdrN hi_end.hdrCap hi_end.hdrL hi_end.hdrP hperm1 hslots1
    hi_end.freeChain hi_end.freeNodeOk hi_end.vertexOk hi_end.edgeOk hi_end.auxPathOk
    hi_end.subdivOk hfin_lt hfin_sp (fun _ _ => rfl)
  refine ⟨s_end + 1, _, _, _, hrun, hexit.1, hexit.2.1, ?_,
    cut_canonRoot hrep₀ hexit.1 hgood_par hbad_par⟩
  show _ + (s_end + 1 - hp_caller) + lctPhi L st_end.mem b F.n ≤ _
  exact cut_top_budget hbd_mid hle_end

end CutTop

end MinCostFlow.LinkCut.Prog
