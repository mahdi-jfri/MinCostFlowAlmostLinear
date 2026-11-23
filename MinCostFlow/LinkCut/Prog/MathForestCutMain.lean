module

public import MinCostFlow.LinkCut.Prog.MathForestCutEdge

/-!
# The main branch of `cut`

This file runs `lctCutMainBody`, the part of `cut` used when both vertices exist. It calls
`reroot (x + 1)` and `expose (y + 1)`. If the exposed path does not have exactly two vertices,
then `x` and `y` are not adjacent and nothing more happens. Otherwise the edge step
(`lctCutEdgeBody_runs`) finishes the work. The result, `lctCutMainBody_runs`, gives the
invariants of `F.cut x y` at the end, and bounds the cost of the branch by
`C_CUT_OP L * (log (n + 2) + 1)` in the amortized sense.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutMainArith

private lemma cut_coeff_le (L : ℕ) :
    C_REROOT_OP L + C_EXPOSE_OP L + 3 * K_SPLAY_STEP L + C_SPLAY_CONST L + 2 * C_HEAVY L + 600 ≤
      C_CUT_OP L := by
  have hks : K_SPLAY_STEP L ≤ 9200 * (L + 1) := by
    unfold K_SPLAY_STEP K_DOUBLE K_PUSH_PATH K_ROTATE K_PUSH_DOWN K_PULL; omega
  have hch := c_heavy_le L
  unfold C_REROOT_OP C_EXPOSE_OP C_SPLAY_CONST C_CUT_OP
  omega

/-- The budget of the main branch, with the products by `logN` kept as single terms. -/
private lemma cut_main_budget {c_re c_exp c_e s2 s_e hp phi0 phi2 phi_e
    cre k3 cs ch2 ccut : ℕ}
    (h1 : c_re + c_exp + (s2 - hp) + phi2 ≤ phi0 + cre)
    (h2 : c_e + (s_e - s2) + phi_e ≤ phi2 + k3 + cs + ch2 + 400)
    (hle2 : hp ≤ s2) (hle_e : s2 ≤ s_e)
    (hcoef : cre + k3 + cs + ch2 + 600 ≤ ccut) :
    c_re + c_exp + c_e + 50 + 60 + (s_e - hp) + phi_e ≤ phi0 + ccut := by
  omega

private lemma cut_main_coeff_mul (L logN : ℕ) (hlog : 1 ≤ logN) :
    (C_REROOT_OP L + C_EXPOSE_OP L) * logN + 3 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L +
      2 * C_HEAVY L + 600 ≤ C_CUT_OP L * logN := by
  have h := Nat.mul_le_mul_right logN (cut_coeff_le L)
  have hcs : C_SPLAY_CONST L ≤ C_SPLAY_CONST L * logN := Nat.le_mul_of_pos_right _ hlog
  have hch : 2 * C_HEAVY L ≤ 2 * C_HEAVY L * logN := Nat.le_mul_of_pos_right _ hlog
  have h600 : 600 ≤ 600 * logN := Nat.le_mul_of_pos_right _ hlog
  have hexp : (C_REROOT_OP L + C_EXPOSE_OP L + 3 * K_SPLAY_STEP L + C_SPLAY_CONST L +
      2 * C_HEAVY L + 600) * logN = (C_REROOT_OP L + C_EXPOSE_OP L) * logN +
      3 * K_SPLAY_STEP L * logN + C_SPLAY_CONST L * logN + 2 * C_HEAVY L * logN +
      600 * logN := by ring
  omega

private lemma cut_room_re {hp phi0 a b m p2w : ℕ} (hab : a ≤ b)
    (h : hp + phi0 + b + m + 1 < p2w) : hp + phi0 + a + m + 1 < p2w := by
  omega

private lemma cut_room_splay {c s2 hp phi0 phi2 cre ccut m6 m7 p2w : ℕ}
    (h1 : c + (s2 - hp) + phi2 ≤ phi0 + cre) (hle : hp ≤ s2) (hcr : cre ≤ ccut)
    (hm : m6 ≤ m7) (h : hp + phi0 + ccut + m7 + 1 < p2w) : s2 + m6 < p2w := by
  omega

end CutMainArith

section CutMainRun

/-- The branch of `cut` for `x < n` and `y < n`, started with the heap pointer stored in the
header. It ends with the invariants of `F.cut x y` and pays at most
`C_CUT_OP L * (log (n + 2) + 1)` with `60` to spare. -/
theorem lctCutMainBody_runs {w h L P b x y hp_caller pos : ℕ}
    {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (regs : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hx : x < F.n) (hy : y < F.n)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hroom : hp_caller + lctPhi L mem₀ b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w)
    (hr0 : regs 0 = b) (hr1 : regs 1 = x) (hr2 : regs 2 = y)
    (ω : ℕ → Bool) :
    let nb := lctNodesBase b
    let cap := lctCap F.n
    let mem₁ := Function.update mem₀ (nb - 1) hp_caller
    ∃ st_end c free1 edgeMap1 trees1 mem_safe,
      Runs w p ω (lctCutMainBody lp) { mem := mem₁, regs := regs, pos := pos } .normal
        st_end c ∧
      st_end.regs 0 = b ∧
      LctExposeInvs w h L P b F.n free1 edgeMap1 trees1 st_end.mem ∧
      (edgeMap1.map Prod.snd).Perm (F.cut x y).edges ∧
      ((edgeMap1.map Prod.fst) ++ free1).Perm ((List.range F.n).map (F.n + 1 + ·)) ∧
      SafeMem mem_safe nb cap hp_caller st_end.mem ∧
      SlotZeroOk mem_safe nb ∧ PtrFootOk b mem_safe x₀ L ∧
      (∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_caller → mem_safe a = mem₀ a) ∧
      hp_caller ≤ st_end.mem (nb - 1) ∧
      c + 60 + (st_end.mem (nb - 1) - hp_caller) + lctPhi L st_end.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      ∃ par₂, RootMove (lctAuxParent mem₀ nb cap) par₂ cap (x + 1) ∧
        CutParShape par₂ (lctAuxParent st_end.mem nb cap) F x y := by
  dsimp only
  have hlog : 1 ≤ Nat.log 2 (F.n + 2) + 1 := by omega
  have hcoef := cut_main_coeff_mul L (Nat.log 2 (F.n + 2) + 1) hlog
  have hcre_le : (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) ≤
      C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) := by omega
  have hroom_re : hp_caller + lctPhi L mem₀ b F.n +
      (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w :=
    cut_room_re hcre_le hroom
  obtain ⟨st₁, st₂, c_re, c_exp, l₂, rest₂, x₂, hrun_re, hrun_exp, hi₂, hsafe₂, _, hle₂,
      hpp₂, _, _, _, hhead_same, hlast_v, hcost_re, hrep₂, hx2_trees, hz0_safe, hpf0, hag0,
      harena_eff, _, _, hmove₂⟩ :=
    rerootExpose_runs (u := x) (v := y) (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hrep₀
      hx hy hfoot hz₀ le_rfl hroom_re ω
  set nb := lctNodesBase b with hnb
  set cap := lctCap F.n with hcap_def
  set logN := Nat.log 2 (F.n + 2) + 1 with hlogN
  have harena_def : lctArenaHi b cap = nb + NODE_STRIDE * (cap + 1) := rfl
  have hroom_arena : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := by omega
  obtain ⟨c_set, hrun_set, hc_set⟩ := cut_mainSetup_runs (p := p) (ω := ω) (pos := pos)
    (mem := Function.update mem₀ (nb - 1) hp_caller) hr0 hr1 hr2 hx hy hroom_arena
  set regs_s := Function.update (Function.update (Function.update (Function.update
    (Function.update regs 5 nb) 6 (x + 1)) 7 (y + 1)) 8 (nb + NODE_STRIDE * (y + 1))) 15
    (nb + NODE_STRIDE * (x + 1)) with hregs_s
  set regs_e := Function.update (Function.update regs_s 25 0) 25 (y + 1) with hregs_e
  have he0 : regs_e 0 = b := by simp [regs_e, regs_s, hr0]
  have he1 : regs_e 1 = x := by simp [regs_e, regs_s, hr1]
  have he2 : regs_e 2 = y := by simp [regs_e, regs_s, hr2]
  have he5 : regs_e 5 = nb := by simp [regs_e, regs_s]
  have he8 : regs_e 8 = nb + NODE_STRIDE * (y + 1) := by simp [regs_e, regs_s]
  have he15 : regs_e 15 = nb + NODE_STRIDE * (x + 1) := by simp [regs_e, regs_s]
  have heval_re : evalArgs w
      { mem := Function.update mem₀ (nb - 1) hp_caller, regs := regs_s, pos := pos }
      [.reg 5, .reg 6] = some [nb, x + 1] :=
    WordRAM.evalArgs_cons (Expr.eval_reg_of_eq (by simp [regs_s]))
      (WordRAM.evalArgs_cons (Expr.eval_reg_of_eq (by simp [regs_s]))
        (WordRAM.evalArgs_nil w _))
  have heval_exp : evalArgs w
      { mem := st₁.mem, regs := Function.update regs_s 25 0, pos := st₁.pos }
      [.reg 5, .reg 7] = some [nb, y + 1] :=
    WordRAM.evalArgs_cons (Expr.eval_reg_of_eq (by simp [regs_s]))
      (WordRAM.evalArgs_cons (Expr.eval_reg_of_eq (by simp [regs_s]))
        (WordRAM.evalArgs_nil w _))
  have hargs : argsSize [Expr.reg 5, Expr.reg 6] = 2 ∧ argsSize [Expr.reg 5, Expr.reg 7] = 2 :=
    ⟨by decide, by decide⟩
  -- The test on the number of vertices of the exposed path.
  set vc := nodeField st₂.mem nb (y + 1) OFF_VCNT with hvc_def
  have h1w : 1 < 2 ^ w := by omega
  have hcap2 : cap = 2 * F.n := rfl
  have hy_node : nb + NODE_STRIDE * (y + 1) + NODE_STRIDE < 2 ^ w := by
    have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : y + 1 + 1 ≤ cap + 1)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  let st_e : State := { mem := st₂.mem, regs := regs_e, pos := st₂.pos }
  have hvc_eval : Expr.eval w st_e
      (.bin .eq (.load (.bin .add (.reg 8) (.const OFF_VCNT))) (.const 2)) =
      some (if vc = 2 then 1 else 0) :=
    Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq he8)
      (Expr.eval_const (by unfold OFF_VCNT NODE_STRIDE at *; omega))
      (by unfold OFF_VCNT NODE_STRIDE at *; omega)) rfl)
      (Expr.eval_const (by omega)) h1w
  have hsize_vc : (Expr.bin .eq (.load (.bin .add (.reg 8) (.const OFF_VCNT)))
      (.const 2)).size = 6 := rfl
  have hroom_sp : st₂.mem (nb - 1) + 6000 * (L + 1) * (F.n + 2) < 2 ^ w :=
    cut_room_splay hcost_re hle₂ hcre_le
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))) hroom
  -- Assemble the run of the main branch from the run of the final test.
  have hassemble : ∀ {st_end : State} {c_t : ℕ},
      Runs w p ω (.cond (.bin .eq (.load (.bin .add (.reg 8) (.const OFF_VCNT))) (.const 2))
        (lctCutEdgeBody lp) .nop) st_e .normal st_end c_t →
      Runs w p ω (lctCutMainBody lp)
        { mem := Function.update mem₀ (nb - 1) hp_caller, regs := regs, pos := pos } .normal
        st_end (c_set + (2 + c_re + 1 + (2 + c_exp + 1 + c_t + 1) + 1) + 1) := by
    intro st_end c_t hcond
    have hexp_chain := link_runs_seq_call_runs heval_exp hexpose_eq hrun_exp hcond
    have hre_chain := link_runs_seq_call_runs heval_re hreroot_eq hrun_re hexp_chain
    rw [hargs.1, hargs.2] at hre_chain
    exact link_runs_seq_normal hrun_set hre_chain
  by_cases hvc2 : vc = 2
  · obtain ⟨st_end, c_e, free1, edgeMap1, trees1, mem_safe, hrun_e, hend0, hi_end, hperm1,
        hslots1, hsafe_end, hslot_end, hptr_end, hag_end, hle_end, hbd_e, hshape⟩ :=
      lctCutEdgeBody_runs (pos := st₂.pos) p lp mem₀ (Function.update mem₀ (nb - 1) hp_caller)
        st₂.mem regs_e hp_base hp_sp hrep₀ hi₂ hrep₂ hx2_trees hsafe₂ hz0_safe hpf0 hag0
        (le_trans (le_of_eq rfl) harena_eff) hx hy hpp₂ hhead_same hlast_v hvc2 he0 he1 he2
        he5 he8 he15 hroom_sp ω
    rw [← hnb] at hle_end hbd_e
    rw [← hlogN] at hbd_e
    have hcond : Runs w p ω (.cond (.bin .eq (.load (.bin .add (.reg 8) (.const OFF_VCNT)))
        (.const 2)) (lctCutEdgeBody lp) .nop) st_e .normal st_end (6 + c_e + 1) :=
      runs_cond_iff.2 ⟨1, c_e, by simp only [hvc_eval, hvc2, ↓reduceIte], by simpa using hrun_e, rfl⟩
    refine ⟨st_end, _, free1, edgeMap1, trees1, mem_safe, hassemble hcond, hend0, hi_end, hperm1,
      hslots1, hsafe_end, hslot_end, hptr_end, hag_end, le_trans hle₂ hle_end, ?_,
      _, hmove₂, hshape⟩
    have hbd := cut_main_budget (c_e := c_e) hcost_re hbd_e hle₂ hle_end hcoef
    omega
  · have hcut : F.cut x y = F := by
      by_cases hxy : x = y
      · exact cut_eq_self_of_bad_args hrep₀.valid (Or.inr (Or.inr hxy))
      · exact cut_eq_self_of_vcnt_ne_two hi₂ hrep₂ hrep₀.edgeMap_snd_perm hrep₀.slots_perm
          (by rw [hx2_trees]; simp) hx hy hxy rfl hpp₂ hhead_same hlast_v hvc2
    have hcond : Runs w p ω (.cond (.bin .eq (.load (.bin .add (.reg 8) (.const OFF_VCNT)))
        (.const 2)) (lctCutEdgeBody lp) .nop) st_e .normal st_e (6 + 1 + 1) :=
      runs_cond_iff.2 ⟨0, 1, by simp only [hvc_eval, hvc2, ↓reduceIte],
        by simpa using runs_nop_iff.2 ⟨rfl, rfl, rfl⟩, rfl⟩
    refine ⟨st_e, _, x₀.freeEdges, x₀.edgeMap, _, Function.update mem₀ (nb - 1) hp_caller,
      hassemble hcond, he0, hi₂, by rw [hcut]; exact hrep₀.edgeMap_snd_perm, hrep₀.slots_perm,
      hsafe₂, hz0_safe, hpf0, hag0, hle₂, ?_, _, hmove₂, Or.inl ⟨fun _ => rfl, hcut⟩⟩
    have hbd := cut_main_budget (c_e := 0) (s_e := st₂.mem (nb - 1)) (phi_e := lctPhi L st₂.mem b F.n)
      hcost_re (by omega) hle₂ le_rfl hcoef
    show _ + 60 + (st₂.mem (nb - 1) - hp_caller) + lctPhi L st₂.mem b F.n ≤ _
    omega

end CutMainRun

end MinCostFlow.LinkCut.Prog
