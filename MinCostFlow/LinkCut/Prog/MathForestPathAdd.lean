module

public import MinCostFlow.LinkCut.Prog.MathForestPathAddInvs

/-!
# Word-RAM Operation `pathAdd` for `MathForest`

Implements deterministic (`Stmt.NoRand`) `lctPathAddBody` taking `args = [b, u, v, dPtr, dNeg, hp_caller]`
and proves `lctPathAddBody_runs` establishing `LctMemRep` for `F.pathAdd u v δ`, `DSRep.Respects`,
and the `O((L + 1) log (n + 2))` amortized cost bound (van den Brand et al., `arXiv:2309.16629v1`,
Lemma 4.1 p. 13, from [KangP15] Section 4).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PathAddProcedure

/-- Amortized constant coefficient for `pathAdd` (covers `reroot + expose + copyWords + applyTag`). -/
def C_PATHADD_OP (L : ℕ) : ℕ := 310000 * (L + 1)

/-- `else` branch (`u ≠ v`) of `lctPathAddBody` after setting registers `6..13`:
copies `[dPtr, dPtr + L)` to `[hp_caller, hp_caller + L)`, reserves `hp_eff = hp_caller + L`
in `LCT_HDR_HP`, rerroots `u`, exposes `v`, calls `applyTag` on `v + 1`, and returns the new
heap pointer via `LCT_HDR_HP`. -/
def lctPathAddElseBody (lp : LctProcs) : Stmt :=
  .call 15 lp.copyWords [.reg 9, .reg 8, .reg 7] ;;
  .assign 14 (.bin .add (.reg 8) (.reg 7)) ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 14) ;;
  .call 15 lp.reroot [.reg 11, .reg 12] ;;
  .call 15 lp.expose [.reg 11, .reg 13] ;;
  .call 15 lp.splay.applyTag [.reg 11, .reg 13, .reg 8, .reg 10] ;;
  .assign 14 (.load (.bin .add (.reg 6) (.const LCT_HDR_HP))) ;;
  .ret (.bin .add (.reg 14) (.const 1))

/-- Deterministic Word-RAM `pathAdd` body taking `args = [b, u, v, dPtr, dNeg, hp_caller]`.
When `u = v`, returns `hp_caller` unchanged; otherwise copies the `L`-limb delta into `[hp_caller, hp_caller + L)`,
rerroots `u`, exposes `v`, calls `applyTag` on `v + 1`, and returns `hp_final`. -/
def lctPathAddBody (lp : LctProcs) : Stmt :=
  .cond (.bin .eq (.reg 1) (.reg 2))
    (.ret (.reg 5))
    (.assign 6 (.reg 0) ;;
     .assign 7 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
     .assign 8 (.reg 5) ;;
     .assign 9 (.reg 3) ;;
     .assign 10 (.reg 4) ;;
     .assign 11 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)) ;;
     .assign 12 (.bin .add (.reg 1) (.const 1)) ;;
     .assign 13 (.bin .add (.reg 2) (.const 1)) ;;
     lctPathAddElseBody lp)

theorem lctPathAddBody_noRand (lp : LctProcs) : (lctPathAddBody lp).NoRand := by
  simp [lctPathAddBody, lctPathAddElseBody, Stmt.NoRand]

private lemma pathAdd_room_re_arith {hp L phi0 c_rexp_log cp_log m p2w : ℕ}
    (hk : c_rexp_log ≤ cp_log)
    (hbd : hp + phi0 + cp_log + m + L + 1 < p2w) :
    (hp + L) + phi0 + c_rexp_log + m + 1 < p2w := by
  omega

private lemma pathAdd_room_tag_arith {c_re c_exp s hp L phi0 phi2 c_rexp_log cp_log ktag m7 p2w : ℕ}
    (h1 : c_re + c_exp + (s - (hp + L)) + phi2 ≤ phi0 + c_rexp_log)
    (hle : hp + L ≤ s) (hk : c_rexp_log ≤ cp_log) (hkt : ktag ≤ m7)
    (hbd : hp + phi0 + cp_log + m7 + L + 1 < p2w) :
    s + ktag < p2w := by
  omega

private lemma pathAdd_hk_mul_arith {L c_rexp ck cs c_pa logN : ℕ}
    (hk : c_rexp + ck + cs + 20 * L + 200 ≤ c_pa) (hlog : 1 ≤ logN) :
    c_rexp * logN + ck + cs + 20 * L + 200 ≤ c_pa * logN := by
  have h1 : ck + cs + 20 * L + 200 ≤ (ck + cs + 20 * L + 200) * logN :=
    Nat.le_mul_of_pos_right _ hlog
  have h2 : (c_rexp + (ck + cs + 20 * L + 200)) * logN =
      c_rexp * logN + (ck + cs + 20 * L + 200) * logN := by ring
  have h3 : (c_rexp + (ck + cs + 20 * L + 200)) * logN ≤ c_pa * logN := by
    simpa only [Nat.add_assoc] using Nat.mul_le_mul_right logN hk
  omega

private lemma pathAdd_cost_arith {c_tot c_re c_exp c_tag s2 s3 hp L phi0 phi3 cr_log ck cp_log c_cp space p2w m7 : ℕ}
    (h12 : c_re + c_exp + (s2 - (hp + L)) + phi3 ≤ phi0 + cr_log)
    (h23 : c_tag + (s3 - s2) ≤ ck) (hcp : c_cp ≤ 17 * L + 10)
    (hle2 : hp + L ≤ s2) (hle3 : s2 ≤ s3)
    (hct : c_tot ≤ c_re + c_exp + c_cp + c_tag + 150)
    (hk : cr_log + ck + 17 * L + 20 * L + 200 ≤ cp_log)
    (hsp : phi0 + cp_log + L + 1 ≤ space)
    (hbd : hp + phi0 + cp_log + m7 + L + 1 < p2w) :
    s3 + 1 < p2w ∧ s3 + 1 ≤ hp + space ∧
      c_tot + (s3 + 1 - hp) + phi3 ≤ phi0 + cp_log := by
  omega

private lemma pathAdd_ctot_arith {c_re c_exp c_cp c_tag : ℕ} :
    3 + (2 + (5 + (2 + (2 + (2 + (4 + (4 + (4 + ((3 + c_cp + 1) + (4 + (5 +
      ((2 + c_re + 1) + ((2 + c_exp + 1) + ((4 + c_tag + 1) + (5 + 4 + 1) + 1) + 1) + 1) +
      1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
    c_re + c_exp + c_cp + c_tag + 150 := by
  have hsum :
      3 + (2 + (5 + (2 + (2 + (2 + (4 + (4 + (4 + ((3 + c_cp + 1) + (4 + (5 +
        ((2 + c_re + 1) + ((2 + c_exp + 1) + ((4 + c_tag + 1) + (5 + 4 + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 =
      c_re + c_exp + c_cp + c_tag + 77 := by ring
  omega



theorem lctPathAddBody_runs {w h L P b u v dPtr dNeg hp_caller space pos : ℕ}
    {F : MathForest} {x₀ : LctConc} {δ : ℚ} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : u < F.n) (hv : v < F.n) (hsc : F.SameComp u v)
    (hdNeg : dNeg ≤ 1) (hdPtr : Valid mem₀ dPtr h L) (hdPtr_le : dPtr + L ≤ hp_caller)
    (hδ : ((if dNeg = 0 then intVal mem₀ dPtr h L else -intVal mem₀ dPtr h L : ℤ) : ℚ) /
      (2 : ℚ) ^ P = δ)
    (hfit_F : ∀ e ∈ (F.pathAdd u v δ).edges, EdgeFits h L P e)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hhp_bd : hp_caller + lctPhi L mem₀ b F.n + C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + L + 1 < 2 ^ w)
    (hsp_ge : lctPhi L mem₀ b F.n + C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) + L + 1 ≤ space)
    (ω : ℕ → Bool) :
    ∃ hp_final st' c x',
      Runs w p ω (lctPathAddBody lp) (startState [b, u, v, dPtr, dNeg, hp_caller] mem₀ pos)
        (.returned hp_final) st' c ∧
      LctMemRep w h L P b (F.pathAdd u v δ) x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_final b x' st'.mem ∧
      c + (hp_final - hp_caller) + lctPhi L st'.mem b (F.pathAdd u v δ).n ≤
        lctPhi L mem₀ b F.n + C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) ∧
      (u ≠ v → RerootRoots mem₀ st'.mem b F u) := by
  have hlog_pos : 1 ≤ Nat.log 2 (F.n + 2) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  let st_init := startState [b, u, v, dPtr, dNeg, hp_caller] mem₀ pos
  have hst_init_args : st_init.regs 0 = b ∧ st_init.regs 1 = u ∧ st_init.regs 2 = v ∧
      st_init.regs 3 = dPtr ∧ st_init.regs 4 = dNeg ∧ st_init.regs 5 = hp_caller := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [st_init, startState]
  have hhp_eff_w : hp_caller + L < 2 ^ w := room_lt_pow6 (by omega : L ≤ L) hhp_bd
  have hhp_w : hp_caller < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hhp_eff_w
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with
    ⟨harena_hp, hnb_w, hb_w, h36_w, _hstr_w, hbh_lt, hbh_hp, hfn1_w, _⟩
  have hcond_eq : Expr.eval w st_init (.bin .eq (.reg 1) (.reg 2)) = some (if u = v then 1 else 0) := by
    have hw1 : (if u = v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simpa [BinOp.eval] using Expr.eval_bin (op := .eq)
      (Expr.eval_reg_of_eq (w := w) (st := st_init) hst_init_args.2.1)
      (Expr.eval_reg_of_eq (w := w) (st := st_init) hst_init_args.2.2.1)
      (by simpa [BinOp.eval] using hw1)
  by_cases huv : u = v
  · subst huv
    have hpa_self : F.pathAdd u u δ = F := by
      have happ0 : MathForest.applyStepsDelta [] δ = id := by
        funext e; simp [MathForest.applyStepsDelta]
      simp [MathForest.pathAdd, MathForest.findSteps_self, happ0]
    rw [hpa_self]
    have hret : Runs w p ω (.ret (.reg 5)) st_init (.returned hp_caller) st_init 2 :=
      runs_ret_iff.mpr ⟨hp_caller, Expr.eval_reg_of_eq (w := w) (st := st_init) hst_init_args.2.2.2.2.2,
        rfl, rfl, by decide⟩
    have hcond : Runs w p ω (lctPathAddBody lp) st_init (.returned hp_caller) st_init (3 + 2 + 1) := by
      rw [lctPathAddBody, runs_cond_iff]
      refine ⟨1, 2, by simpa using hcond_eq, ?_, by decide⟩
      simp only [Nat.one_ne_zero, ↓reduceIte]
      exact hret
    have hresp0 : (lctDSRep w h L P).Respects (lctFoot b x₀) hp_caller space mem₀ hp_caller b x₀ mem₀ :=
      ⟨le_rfl, Nat.le_add_right _ _, hz₀, fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩
    have hcost0 : 3 + 2 + 1 + (hp_caller - hp_caller) + lctPhi L mem₀ b F.n ≤
        lctPhi L mem₀ b F.n + C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) := by
      have hc_lb : 6 ≤ C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) := by
        have h1 : 6 ≤ C_PATHADD_OP L := by unfold C_PATHADD_OP; omega
        exact le_trans h1 (Nat.le_mul_of_pos_right _ hlog_pos)
      omega
    exact ⟨hp_caller, st_init, 3 + 2 + 1, x₀, hcond, hrep₀, hresp0, hcost0,
      fun hne => absurd rfl hne⟩
  · let nb := lctNodesBase b
    let cap := lctCap F.n
    let hp_eff := hp_caller + L
    let mem_base := Function.update mem₀ (nb - 1) hp_caller
    rcases enterOp_invs hrep₀ hfoot hz₀ le_rfl hhp_w with
      ⟨hi_base, _, _, _, hslot0_base, hpf0_base, _, hag0_base⟩
    have hL_mem₀ : mem₀ (b + LCT_HDR_L) = L := by
      have hne : b + LCT_HDR_L ≠ nb - 1 := by
        rw [← hbh_hp]; unfold LCT_HDR_L LCT_HDR_HP; omega
      have hbl : mem_base (b + LCT_HDR_L) = L := hi_base.hdrL
      simpa [mem_base, Function.update_of_ne hne] using hbl
    have hu1_w : u + 1 < 2 ^ w := by omega
    have hv1_w : v + 1 < 2 ^ w := by omega
    have hL_w : L < 2 ^ w := by omega
    let s1 : State := { st_init with regs := Function.update st_init.regs 6 b }
    let s2 : State := { s1 with regs := Function.update s1.regs 7 L }
    let s3 : State := { s2 with regs := Function.update s2.regs 8 hp_caller }
    let s4 : State := { s3 with regs := Function.update s3.regs 9 dPtr }
    let s5 : State := { s4 with regs := Function.update s4.regs 10 dNeg }
    let s6 : State := { s5 with regs := Function.update s5.regs 11 nb }
    let s7 : State := { s6 with regs := Function.update s6.regs 12 (u + 1) }
    let s8 : State := { s7 with regs := Function.update s7.regs 13 (v + 1) }
    have hs1 : Runs w p ω (.assign 6 (.reg 0)) st_init .normal s1 2 :=
      runs_assign_iff.mpr ⟨b, Expr.eval_reg_of_eq hst_init_args.1, rfl, rfl, by decide⟩
    have hs2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const LCT_HDR_L)))) s1 .normal s2 5 := by
      refine runs_assign_iff.mpr ⟨L, ?_, rfl, rfl, by decide⟩
      have hadd := Expr.eval_add (Expr.eval_reg_of_eq (st := s1) (r := 0) (by simp [s1, hst_init_args]))
        (Expr.eval_const (lt_trans (by decide : LCT_HDR_L < 36) h36_w)) hbh_lt
      rw [Expr.eval_load hadd]; exact congrArg some hL_mem₀
    have hs3 : Runs w p ω (.assign 8 (.reg 5)) s2 .normal s3 2 :=
      runs_assign_iff.mpr ⟨hp_caller, Expr.eval_reg_of_eq (st := s2) (r := 5)
        (by simp [s2, s1, hst_init_args]), rfl, rfl, by decide⟩
    have hs4 : Runs w p ω (.assign 9 (.reg 3)) s3 .normal s4 2 :=
      runs_assign_iff.mpr ⟨dPtr, Expr.eval_reg_of_eq (st := s3) (r := 3)
        (by simp [s3, s2, s1, hst_init_args]), rfl, rfl, by decide⟩
    have hs5 : Runs w p ω (.assign 10 (.reg 4)) s4 .normal s5 2 :=
      runs_assign_iff.mpr ⟨dNeg, Expr.eval_reg_of_eq (st := s4) (r := 4)
        (by simp [s4, s3, s2, s1, hst_init_args]), rfl, rfl, by decide⟩
    have hs6 : Runs w p ω (.assign 11 (.bin .add (.reg 0) (.const LCT_HDR_SIZE))) s5 .normal s6 4 :=
      runs_assign_iff.mpr ⟨nb, Expr.eval_add
        (Expr.eval_reg_of_eq (st := s5) (r := 0) (by simp [s5, s4, s3, s2, s1, hst_init_args]))
        (Expr.eval_const (lt_trans (by decide : LCT_HDR_SIZE < 36) h36_w)) hnb_w, rfl, rfl, by decide⟩
    have hs7 : Runs w p ω (.assign 12 (.bin .add (.reg 1) (.const 1))) s6 .normal s7 4 :=
      runs_assign_iff.mpr ⟨u + 1, Expr.eval_add
        (Expr.eval_reg_of_eq (st := s6) (r := 1) (by simp [s6, s5, s4, s3, s2, s1, hst_init_args]))
        (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hu1_w, rfl, rfl, by decide⟩
    have hs8 : Runs w p ω (.assign 13 (.bin .add (.reg 2) (.const 1))) s7 .normal s8 4 :=
      runs_assign_iff.mpr ⟨v + 1, Expr.eval_add
        (Expr.eval_reg_of_eq (st := s7) (r := 2) (by simp [s7, s6, s5, s4, s3, s2, s1, hst_init_args]))
        (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w)) hv1_w, rfl, rfl, by decide⟩
    have hrs8_ok : s8.regs 0 = b ∧ s8.regs 6 = b ∧ s8.regs 7 = L ∧ s8.regs 8 = hp_caller ∧
        s8.regs 9 = dPtr ∧ s8.regs 10 = dNeg ∧ s8.regs 11 = nb ∧ s8.regs 12 = u + 1 ∧
        s8.regs 13 = v + 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [s8, s7, s6, s5, s4, s3, s2, s1, hst_init_args, Function.update_of_ne]
    have hd_args_w : ∀ a ∈ [dPtr, hp_caller, L], a < 2 ^ w := by
      intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> omega
    have hpre_cp : (copyWordsContract w).pre [dPtr, hp_caller, L] mem₀ :=
      ⟨dPtr, hp_caller, L, rfl, lt_trans (by decide) h36_w, by omega, le_of_lt hhp_eff_w, Or.inr hdPtr_le⟩
    rcases hp_base.copyWords_ok [dPtr, hp_caller, L] mem₀ pos ω hd_args_w hpre_cp with
      ⟨body_cp, hcp_eq, o_cp, st_cp, c_cp, hrun_cp, hpost_cp, hc_cp⟩
    rcases hpost_cp with ⟨_, _, _, hcp_arg, _, hcp_vals, hcp_out⟩
    cases hcp_arg
    let rA := Function.update s8.regs 15 o_cp.value
    have hcall_cp : Runs w p ω (.call 15 lp.copyWords [.reg 9, .reg 8, .reg 7]) s8 .normal
        { mem := st_cp.mem, regs := rA, pos := st_cp.pos } (3 + c_cp + 1) :=
      runs_call_iff.mpr ⟨[dPtr, hp_caller, L], body_cp, o_cp, st_cp, c_cp,
        by simp [evalArgs, Expr.eval, hrs8_ok], hcp_eq,
        by dsimp only [s8, s7, s6, s5, s4, s3, s2, s1, st_init, startState]; exact hrun_cp,
        rfl, by cases st_cp; rfl, rfl⟩
    have hag_cp_foot : ∀ a, lctFoot b x₀ a → mem₀ a = st_cp.mem a := fun a ha =>
      (hcp_out a (Or.inl (hfoot a ha))).symm
    have hloc_cp := lctDSRep_local w h L P b F x₀ mem₀ st_cp.mem hag_cp_foot
    have hrep_cp : LctMemRep w h L P b F x₀ st_cp.mem := hloc_cp.1 hrep₀
    have hphi_cp : lctPhi L st_cp.mem b F.n = lctPhi L mem₀ b F.n := by
      simpa [lctDSRep, hrep₀.2.2.2.2.1] using hloc_cp.2.symm
    have hrA_ok : rA 0 = b ∧ rA 6 = b ∧ rA 7 = L ∧ rA 8 = hp_caller ∧ rA 10 = dNeg ∧
        rA 11 = nb ∧ rA 12 = u + 1 ∧ rA 13 = v + 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [rA, hrs8_ok, Function.update_of_ne]
    let rA14 := Function.update rA 14 hp_eff
    have hs_eff : Runs w p ω (.assign 14 (.bin .add (.reg 8) (.reg 7)))
        { mem := st_cp.mem, regs := rA, pos := st_cp.pos } .normal
        { mem := st_cp.mem, regs := rA14, pos := st_cp.pos } 4 :=
      runs_assign_iff.mpr ⟨hp_eff, Expr.eval_add
        (Expr.eval_reg_of_eq (st := { mem := st_cp.mem, regs := rA, pos := st_cp.pos }) hrA_ok.2.2.2.1)
        (Expr.eval_reg_of_eq (st := { mem := st_cp.mem, regs := rA, pos := st_cp.pos }) hrA_ok.2.2.1)
        hhp_eff_w, rfl, rfl, by decide⟩
    let mem₁ := Function.update st_cp.mem (nb - 1) hp_eff
    have hnb1_lt_hp : nb - 1 < hp_caller := by
      have hpos : 1 ≤ nb := by dsimp only [nb, lctNodesBase, LCT_HDR_SIZE]; omega
      have hle : nb ≤ hp_caller :=
        le_trans (Nat.le_add_right _ _) (by simpa [nb, lctArenaHi] using harena_hp)
      omega
    have hs_store_hp : Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 14))
        { mem := st_cp.mem, regs := rA14, pos := st_cp.pos } .normal
        { mem := mem₁, regs := rA14, pos := st_cp.pos } 5 := by
      have hadd : Expr.eval w { mem := st_cp.mem, regs := rA14, pos := st_cp.pos }
          (.bin .add (.reg 0) (.const LCT_HDR_HP)) = some (nb - 1) := by
        rw [← hbh_hp]
        exact Expr.eval_add
          (Expr.eval_reg_of_eq (st := { mem := st_cp.mem, regs := rA14, pos := st_cp.pos })
            (r := 0) (by simp [rA14, hrA_ok, Function.update_of_ne]))
          (Expr.eval_const (lt_trans (by decide : LCT_HDR_HP < 36) h36_w))
          (by rw [hbh_hp]; exact lt_trans hnb1_lt_hp hhp_w)
      exact runs_store_iff.mpr ⟨nb - 1, hp_eff, hadd,
        Expr.eval_reg_of_eq (w := w) (st := { mem := st_cp.mem, regs := rA14, pos := st_cp.pos })
          (r := 14) (Function.update_self 14 hp_eff rA), rfl, rfl, by decide⟩
    have hrexp_le_pa : C_REROOT_OP L + C_EXPOSE_OP L ≤ C_PATHADD_OP L := by
      unfold C_REROOT_OP C_EXPOSE_OP C_PATHADD_OP; omega
    have hrexp_mul_le : (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) ≤
        C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) :=
      Nat.mul_le_mul_right _ hrexp_le_pa
    have hroom_re : (hp_caller + L) + lctPhi L st_cp.mem b F.n +
        (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
        7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w := by
      rw [hphi_cp]
      exact pathAdd_room_re_arith hrexp_mul_le hhp_bd
    have hfoot_eff : ∀ a, lctFoot b x₀ a → a < hp_eff := fun a ha =>
      lt_of_lt_of_le (hfoot a ha) (Nat.le_add_right _ _)
    have hz_eff : ZeroFrom st_cp.mem hp_eff := fun a ha =>
      (hcp_out a (Or.inr ha)).trans (hz₀ a (le_trans (Nat.le_add_right _ _) ha))
    rcases rerootExpose_runs (pos := st_cp.pos) p lp st_cp.mem hp_base hp_sp hexpose_eq hrep_cp
        hu hv hfoot_eff hz_eff le_rfl hroom_re ω with
      ⟨st₁, st₂, c_re, c_exp, l₂, rest₂, x₂, hrun_re, hrun_exp, hi₂, hsafe₂, hz₂, hle₂, hpp₂,
        _hrev₂, _hht₂, _hev₂, hhead_same, hlast_v, hcost_re_exp, hrep₂, hx2_trees, _, _, _, _, _, _, hmove_re⟩
    let rB := Function.update rA14 15 0
    have hrA14_ok : rA14 6 = b ∧ rA14 7 = L ∧ rA14 8 = hp_caller ∧ rA14 10 = dNeg ∧
        rA14 11 = nb ∧ rA14 12 = u + 1 ∧ rA14 13 = v + 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [rA14, hrA_ok, Function.update_of_ne]
    have hcall_re : Runs w p ω (.call 15 lp.reroot [.reg 11, .reg 12])
        { mem := mem₁, regs := rA14, pos := st_cp.pos } .normal
        { mem := st₁.mem, regs := rB, pos := st₁.pos } (2 + c_re + 1) :=
      runs_call_iff.mpr ⟨[nb, u + 1], lctRerootBody lp, .returned 0, st₁, c_re,
        by simp [evalArgs, Expr.eval, hrA14_ok], hreroot_eq, hrun_re, rfl, by cases st₁; rfl, rfl⟩
    let rC := Function.update rB 15 (v + 1)
    have hrB_ok : rB 6 = b ∧ rB 7 = L ∧ rB 8 = hp_caller ∧ rB 10 = dNeg ∧
        rB 11 = nb ∧ rB 13 = v + 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [rB, hrA14_ok, Function.update_of_ne]
    have hcall_exp : Runs w p ω (.call 15 lp.expose [.reg 11, .reg 13])
        { mem := st₁.mem, regs := rB, pos := st₁.pos } .normal
        { mem := st₂.mem, regs := rC, pos := st₂.pos } (2 + c_exp + 1) :=
      runs_call_iff.mpr ⟨[nb, v + 1], exposeBody lp.splay, .returned (v + 1), st₂, c_exp,
        by simp [evalArgs, Expr.eval, hrB_ok], hexpose_eq, hrun_exp, rfl, by cases st₂; rfl, rfl⟩
    have hrC_ok : rC 6 = b ∧ rC 7 = L ∧ rC 8 = hp_caller ∧ rC 10 = dNeg ∧
        rC 11 = nb ∧ rC 13 = v + 1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [rC, hrB_ok, Function.update_of_ne]
    have hdelta_ag : ∀ i < L, st₂.mem (hp_caller + i) = mem₀ (dPtr + i) := fun i hi => by
      have ha_lo : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller + i :=
        le_trans (by simpa [nb, cap, lctArenaHi] using harena_hp) (Nat.le_add_right _ _)
      have ha_hi : hp_caller + i < hp_eff := by omega
      rw [hsafe₂.2.1 _ (Or.inr (Or.inr ⟨ha_lo, ha_hi⟩))]
      rw [Function.update_of_ne (by omega : hp_caller + i ≠ nb - 1), hcp_vals i hi]
    have hval_delta₂ : Valid st₂.mem hp_caller h L := fun i hi => by
      rw [hdelta_ag i hi]; exact hdPtr i hi
    have hint_delta₂ : intVal st₂.mem hp_caller h L = intVal mem₀ dPtr h L :=
      intVal_congr hdelta_ag
    have hnum_delta₂ : NumPtrOk st₂.mem (nb + NODE_STRIDE * (cap + 1)) (st₂.mem (nb - 1)) h L hp_caller :=
      ⟨by have := arenaHi_bounds hrep₀ hfoot hhp_w; unfold lctArenaHi at *; omega,
       by simpa [nb, cap, lctArenaHi] using harena_hp, hle₂, hval_delta₂⟩
    have hk_tag_le7 : K_APPLY_TAG L ≤ 7000 * (L + 1) * (F.n + 2) := by
      unfold K_APPLY_TAG
      have h1 : 700 * (L + 1) ≤ 7000 * (L + 1) := by omega
      exact le_trans h1 (Nat.le_mul_of_pos_right _ (by omega))
    have hcost_re_exp₀ : c_re + c_exp + (st₂.mem (nb - 1) - (hp_caller + L)) + lctPhi L st₂.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) := by
      simpa [hphi_cp] using hcost_re_exp
    have hroom_tag : st₂.mem (nb - 1) + K_APPLY_TAG L < 2 ^ w :=
      pathAdd_room_tag_arith hcost_re_exp₀ hle₂ hrexp_mul_le hk_tag_le7 hhp_bd
    rcases hp_sp with ⟨spB, hspB⟩
    let d : ℤ := if dNeg = 0 then intVal mem₀ dPtr h L else -intVal mem₀ dPtr h L
    let t₂ := AuxTree.node (v + 1) l₂ .leaf
    have hnd_t2 : t₂.toList.Nodup :=
      list_nodup_of_flatMap_nodup
        ((SplayForestOk.perm hi₂.sf).nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)))
        (by simp [t₂])
    have ht2_match := (SplayForestOk.trees_ok hi₂.sf t₂ (by simp [t₂])).2.2
    have hhead_sc := hhead_same hsc
    rcases pathAdd_stepsShiftFit hu hv hrep₀.valid rfl hrep₂ hx2_trees hfit_F hδ hpp₂ hhead_sc hlast_v with
      ⟨steps, hfs, hw, hnd_raw, hfor, hfit_steps⟩
    have hL_hdr2 : st₂.mem (nb - 3) = L := by
      have hbh_L : nb - 3 = b + LCT_HDR_L := by
        dsimp only [nb, lctNodesBase, LCT_HDR_SIZE, LCT_HDR_L]; omega
      rw [hbh_L, hi₂.hdrL]
    have hbase_w : nb + NODE_STRIDE * (cap + 1) < 2 ^ w := by
      have hhi := hi₂.sf.2.2.2.1
      dsimp only [cap]
      omega
    have hdmod : d % (capacity h L : ℤ) =
        (if dNeg = 0 then intVal st₂.mem hp_caller h L else -intVal st₂.mem hp_caller h L) %
          (capacity h L : ℤ) := by
      dsimp only [d]; rw [hint_delta₂]
    rcases applyTagBody_runs_subtree st₂.pos hp_base.splay_ok hbase_w hi₂.sf.2.2.1
        hL_hdr2 hi₂.sf.2.2.2.1 hz₂ hroom_tag hi₂.sf.2.2.2.2.2.2.2.1 ht2_match hnd_t2 hdNeg
        hnum_delta₂ hdmod hfit_steps ω with
      ⟨st_tag, c_tag, hrun_tag, hc_tag_le, hle_tag, ht2_match_tag, hsteps_tag, hf1_tag, hf2_tag, hfr_tag⟩
    have hsafe₂_base : SafeMem mem_base nb cap hp_caller st₂.mem :=
      pathAdd_safeMem_weaken rfl hbh_hp.symm (by simpa [nb, cap, lctArenaHi] using harena_hp)
        hcp_out hsafe₂
    let st_tag_in := startState [nb, v + 1, hp_caller, dNeg] st₂.mem st₂.pos
    have hrun_tag' : Runs w p ω (applyTagBody (SplayProcs.atBase spB))
        st_tag_in (.returned 0) st_tag c_tag := by
      simpa [st_tag_in, hspB, t₂, AuxTree.rootId] using hrun_tag
    rcases hrun_tag' with ⟨fuel_tag, hex_tag⟩
    have hv1_cap : v + 1 ≤ cap := by dsimp only [cap, lctCap]; omega
    have hsp_hasAt : p.HasAt spB (splayBodies (SplayProcs.atBase spB) h) := by
      simpa [hspB, SplayProcs.atBase] using hp_base.splay_hasAt
    have harena_base : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := by
      simpa [nb, cap, lctArenaHi] using harena_hp
    have hst_tag_r0 : st_tag_in.regs 0 = nb := by simp [st_tag_in, startState]
    have hst_tag_r1 : st_tag_in.regs 1 = v + 1 := by simp [st_tag_in, startState]
    have hst_tag_r2 : PtrAllowed mem_base nb cap hp_caller (st_tag_in.regs 2) := by
      have hr2 : st_tag_in.regs 2 = hp_caller := by simp [st_tag_in, startState]
      rw [hr2]; exact Or.inr (Or.inl le_rfl)
    have hs_tag : SafeMem mem_base nb cap hp_caller st_tag.mem :=
      (applyTag_safeExec hsp_hasAt hi₂.sf.2.2.1 harena_base hv1_cap
        hst_tag_r0 hst_tag_r1 hst_tag_r2 hsafe₂_base hex_tag).2
    have htag_lt_w : st_tag.mem (nb - 1) < 2 ^ w := by omega
    rcases pathAdd_applyTag_invs hv hrep₀.valid hrep₀.edgeMap_snd_perm hrep₀.slots_perm hi₂ hδ
        hle_tag htag_lt_w ht2_match_tag hsteps_tag hf1_tag hf2_tag hfr_tag steps hw hnd_raw hfor with
      ⟨hi_tag, hphi_tag⟩
    let edgeMap' := x₀.edgeMap.map fun q => (q.1, MathForest.applyStepsDelta steps δ q.2)
    let hp_tag := st_tag.mem (nb - 1)
    let hp_final := hp_tag + 1
    let rD := Function.update rC 15 0
    have hcall_tag : Runs w p ω (.call 15 lp.splay.applyTag [.reg 11, .reg 13, .reg 8, .reg 10])
        { mem := st₂.mem, regs := rC, pos := st₂.pos } .normal
        { mem := st_tag.mem, regs := rD, pos := st_tag.pos } (4 + c_tag + 1) :=
      runs_call_iff.mpr ⟨[nb, v + 1, hp_caller, dNeg], applyTagBody lp.splay, .returned 0, st_tag, c_tag,
        by simp [evalArgs, Expr.eval, hrC_ok], hp_base.splay_ok.applyTag_eq, hrun_tag, rfl,
        by cases st_tag; rfl, rfl⟩
    have hrD_ok : rD 6 = b := by simp [rD, hrC_ok, Function.update_of_ne]
    let rE := Function.update rD 14 hp_tag
    have hk_mul : (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
        K_APPLY_TAG L + 17 * L + 20 * L + 200 ≤ C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) :=
      pathAdd_hk_mul_arith (by unfold C_REROOT_OP C_EXPOSE_OP K_APPLY_TAG C_PATHADD_OP; omega) hlog_pos
    let c_tot :=
      3 + (2 + (5 + (2 + (2 + (2 + (4 + (4 + (4 + ((3 + c_cp + 1) + (4 + (5 +
        ((2 + c_re + 1) + ((2 + c_exp + 1) + ((4 + c_tag + 1) + (5 + 4 + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
    have hphi_tag' : lctPhi L st_tag.mem b F.n = lctPhi L st₂.mem b F.n := hphi_tag
    have hcost_re_exp_tag : c_re + c_exp + (st₂.mem (nb - 1) - (hp_caller + L)) +
        lctPhi L st_tag.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) := by
      rw [hphi_tag']; exact hcost_re_exp₀
    rcases pathAdd_cost_arith hcost_re_exp_tag hc_tag_le hc_cp hle₂ hle_tag
        (pathAdd_ctot_arith (c_re := c_re) (c_exp := c_exp) (c_cp := c_cp) (c_tag := c_tag))
        hk_mul hsp_ge hhp_bd with ⟨hfin_lt, hfin_sp, hcost_pa⟩
    have htag_lt_w : hp_tag < 2 ^ w := lt_of_le_of_lt (Nat.le_succ _) hfin_lt
    have hs_ld_hp : Runs w p ω (.assign 14 (.load (.bin .add (.reg 6) (.const LCT_HDR_HP))))
        { mem := st_tag.mem, regs := rD, pos := st_tag.pos } .normal
        { mem := st_tag.mem, regs := rE, pos := st_tag.pos } 5 := by
      have hadd : Expr.eval w { mem := st_tag.mem, regs := rD, pos := st_tag.pos }
          (.bin .add (.reg 6) (.const LCT_HDR_HP)) = some (nb - 1) := by
        rw [← hbh_hp]
        exact Expr.eval_add
          (Expr.eval_reg_of_eq (st := { mem := st_tag.mem, regs := rD, pos := st_tag.pos }) hrD_ok)
          (Expr.eval_const (lt_trans (by decide : LCT_HDR_HP < 36) h36_w))
          (by rw [hbh_hp]; exact lt_trans hnb1_lt_hp hhp_w)
      refine runs_assign_iff.mpr ⟨hp_tag, ?_, rfl, rfl, by decide⟩
      rw [Expr.eval_load hadd]
    have hs_ret : Runs w p ω (.ret (.bin .add (.reg 14) (.const 1)))
        { mem := st_tag.mem, regs := rE, pos := st_tag.pos } (.returned hp_final)
        { mem := st_tag.mem, regs := rE, pos := st_tag.pos } 4 :=
      runs_ret_iff.mpr ⟨hp_final, Expr.eval_add
        (Expr.eval_reg_of_eq (w := w) (st := { mem := st_tag.mem, regs := rE, pos := st_tag.pos })
          (r := 14) (Function.update_self 14 hp_tag rD))
        (Expr.eval_const (lt_trans (by decide : 1 < 36) h36_w))
        hfin_lt, rfl, rfl, by decide⟩
    let hrun_else : Runs w p ω (lctPathAddElseBody lp) _ _ _ _ :=
      runs_seq_normal hcall_cp (runs_seq_normal hs_eff (runs_seq_normal hs_store_hp (runs_seq_normal hcall_re
        (runs_seq_normal hcall_exp (runs_seq_normal hcall_tag (runs_seq_normal hs_ld_hp hs_ret))))))
    have hbranch :=
      runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3 (runs_seq_normal hs4
        (runs_seq_normal hs5 (runs_seq_normal hs6 (runs_seq_normal hs7 (runs_seq_normal hs8 hrun_else)))))))
    have hrun_body : Runs w p ω (lctPathAddBody lp) st_init (.returned hp_final)
        { mem := st_tag.mem, regs := rE, pos := st_tag.pos } c_tot := by
      rw [lctPathAddBody, runs_cond_iff]
      exact ⟨0, _, by simpa [huv] using hcond_eq, by simpa only [↓reduceIte] using hbranch,
        by simp only [Expr.size, c_tot]⟩
    let F1 := F.pathAdd u v δ
    have hF1_n : F1.n = F.n := by
      dsimp only [F1, MathForest.pathAdd]; cases findSteps F.edges u v <;> rfl
    have hF1_val : F1.Valid := F.pathAdd_valid hrep₀.valid u v δ
    have hperme : (edgeMap'.map Prod.snd).Perm F1.edges := by
      dsimp only [edgeMap', F1, MathForest.pathAdd]
      rw [hfs, List.map_map]
      simpa [Function.comp_def] using hrep₀.edgeMap_snd_perm.map (MathForest.applyStepsDelta steps δ)
    have hpermsl : ((edgeMap'.map Prod.fst) ++ x₀.freeEdges).Perm
        ((List.range F1.n).map (F1.n + 1 + ·)) := by
      rw [hF1_n]
      simpa [edgeMap', List.map_map, Function.comp_def] using hrep₀.slots_perm
    have hsf1 : SplayForestOk w h L st_tag.mem nb (lctCap F1.n) (.node (v + 1) l₂ .leaf :: rest₂) := by
      simpa [hF1_n] using hi_tag.sf
    have hfree_nd1 : ∀ ed ∈ x₀.freeEdges, F1.n + 1 ≤ ed ∧ ed ≤ lctCap F1.n ∧
        AuxTree.node ed .leaf .leaf ∈ .node (v + 1) l₂ .leaf :: rest₂ ∧
        nodeField st_tag.mem nb ed OFF_PPAR = 0 ∧
        nodeField st_tag.mem nb ed OFF_ISV = 0 ∧
        nodeField st_tag.mem nb ed OFF_HASE = 0 := by
      simpa [hF1_n] using hi_tag.freeNodeOk
    rcases exitOp_rep hrep₀ hfoot le_rfl hF1_n hF1_val hfit_F hslot0_base hpf0_base hag0_base
        hs_tag hsf1 (by simpa [hF1_n] using hi_tag.hdrN) (by simpa [hF1_n] using hi_tag.hdrCap)
        hi_tag.hdrL hi_tag.hdrP hperme hpermsl hi_tag.freeChain hfree_nd1
        (by simpa [hF1_n] using hi_tag.vertexOk) (by simpa [hF1_n] using hi_tag.edgeOk)
        (by simpa [hF1_n] using hi_tag.auxPathOk) (by simpa [hF1_n] using hi_tag.subdivOk)
        hfin_lt hfin_sp (fun _ _ => rfl) with ⟨hrep1, hresp1, _⟩
    have hFn_pa : (F.pathAdd u v δ).n = F.n := hF1_n
    rw [hFn_pa]
    have hpar_cp : ∀ z, lctAuxParent mem₀ nb cap z = lctAuxParent st_cp.mem nb cap z :=
      lctAuxParent_agree (fun i _ hi =>
        hcp_out i (Or.inl (lt_of_lt_of_le hi harena_base)))
    have hmove₀ : RootMove (lctAuxParent mem₀ nb cap) (lctAuxParent st₂.mem nb cap) cap (u + 1) :=
      (funext hpar_cp) ▸ hmove_re
    have hroots : RerootRoots mem₀ st_tag.mem b F u :=
      hrep₀.rerootRoots_of_rootMove hu (rootMove_of_agree hmove₀ fun z =>
        lctAuxParent_struct_agree (fun y hy off hoff => by
          rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
            exact hf1_tag y hy _ (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)) z)
    exact ⟨hp_final, { mem := st_tag.mem, regs := rE, pos := st_tag.pos }, c_tot, _,
      hrun_body, hrep1, hresp1, by simpa [hp_final, hp_tag, c_tot] using hcost_pa,
      fun _ => hroots⟩

end PathAddProcedure

end MinCostFlow.LinkCut.Prog

