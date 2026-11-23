module

public import MinCostFlow.Final.DynamicLctForestInit
import Mathlib.Tactic

/-!
# The fixed dynamic link-cut forest meets the solver's `forestMachineContract`

Proves `dynLctWrapTail_runs`, `dynLctWrapBody_runs`, `dynLctLinkWrap_runs`,
`dynLctPathMinWrap_runs`, `dynLctPathSumWrap_runs`, `dynLctPathAddWrap_runs`, and
`dynLctForest_implements`: for every `0 < h`, `2 * h + 2 ≤ w`, and `L, P < 2 ^ w`,
if a program places the fixed module `dynLctForestBodies h b0` at `b0`, then it
implements `forestMachineContract lctForestModel w h L P (lctForestRate L) (lctForestAlloc w L N)`
with representation `lctForestRep w h L P N`.
-/

@[expose] public section

namespace MinCostFlow.Final

open WordRAM MinCostFlow.Num MinCostFlow.Rounding MinCostFlow.IPM.Machine
open MinCostFlow.LinkCut.Prog

section DynamicWrapRun

private theorem lctMemRep_hdrL {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    mem (b + LCT_HDR_L) = L := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, hL_eq, _⟩
  exact hL_eq

private theorem wrap_room_q {hp A hp1 c1 phi0 phi1 F Q C M E W : ℕ}
    (hroom : hp + phi0 + (F + Q + C) + M + 18 * A + E + 200 < W)
    (hc1 : c1 + (hp1 - (hp + A)) + phi1 ≤ phi0 + F) (hle1 : hp + A ≤ hp1) :
    hp1 + phi1 + Q + M + E < W ∧ hp1 + A ≤ W := by omega

private theorem wrap_room_cut {hp A hp1 hp2 c1 c2 phi0 phi1 phi2 F Q C M E W : ℕ}
    (hroom : hp + phi0 + (F + Q + C) + M + 18 * A + E + 200 < W)
    (hc1 : c1 + (hp1 - (hp + A)) + phi1 ≤ phi0 + F) (hle1 : hp + A ≤ hp1)
    (hc2 : c2 + (hp2 - hp1) + phi2 ≤ phi1 + Q + 20) (hle2 : hp1 ≤ hp2) :
    hp2 + phi2 + C + M + 1 < W := by omega

private theorem wrap_budget {hp A hp1 hp2 hp3 c1 c2 c3 ccp phi0 phi1 phi2 phi3 F Q C M E W : ℕ}
    (hroom : hp + phi0 + (F + Q + C) + M + 18 * A + E + 200 < W)
    (hc1 : c1 + (hp1 - (hp + A)) + phi1 ≤ phi0 + F) (hle1 : hp + A ≤ hp1)
    (hc2 : c2 + (hp2 - hp1) + phi2 ≤ phi1 + Q + 20) (hle2 : hp1 ≤ hp2)
    (hcp : ccp ≤ 17 * A + 10)
    (hc3 : c3 + (hp3 - hp2) + phi3 ≤ phi2 + C) (hle3 : hp2 ≤ hp3) :
    hp3 < W ∧ hp3 ≤ hp + (phi0 + (F + Q + C) + 18 * A + 200) ∧
    4 + (3 + c1 + 1 + (3 + (c2 + (3 + ccp + 1 + (4 + c3 + 1 + 2 + 1) + 1) + 1) + 1) + 1) + 1 +
      (hp3 - hp) + phi3 ≤ phi0 + (F + Q + C) + 18 * A + 200 := by omega

private theorem wrap_mul3 (a b c k : ℕ) : a * k + b * k + c * k = (a + b + c) * k := by ring

/-- Run of `dynLctWrapTail` when register `rA < 20` (`rA ≠ rh`) holds the answer width `A`. -/
theorem dynLctWrapTail_runs {w h L P b u hp A Cq Eq pos rh rA : ℕ}
    {F F1 : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (regs : ℕ → ℕ) (q : Stmt) (Ans : (ℕ → ℕ) → ℕ → Prop) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hu : u < F.n)
    (hF1n : F1.n = F.n) (hF1v : F1.Valid)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ (hp + A))
    (hr0 : regs 0 = b) (hr1 : regs 1 = u) (hrh : regs rh = hp) (hrA : regs rA = A)
    (hrh20 : rh < 20) (hrA20 : rA < 20)
    (hAns : ∀ m m' a a', Ans m a → (∀ i < A, m' (a' + i) = m (a + i)) → Ans m' a')
    (hq : ∀ mem1 x1 hp1 pos1 regs1,
      LctMemRep w h L P b F x1 mem1 → (∀ a, lctFoot b x1 a → a < hp1) → ZeroFrom mem1 hp1 →
      hp + A ≤ hp1 →
      hp1 + lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) +
        Eq < 2 ^ w →
      (∀ i < 20, regs1 i = regs i) → regs1 21 = hp1 →
      (∀ i < A, mem1 (hp + i) = mem₀ (hp + i)) →
      ∃ (hp2 : ℕ) (st2 : State) (c2 : ℕ) (x2 : LctConc),
        Runs w p ω q { mem := mem1, regs := regs1, pos := pos1 } .normal
          { mem := st2.mem, regs := Function.update regs1 23 hp2, pos := st2.pos } c2 ∧
        LctMemRep w h L P b F1 x2 st2.mem ∧
        (lctDSRep w h L P).Respects (lctFoot b x1) hp1
          (lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + Eq) mem1 hp2 b x2 st2.mem ∧
        c2 + (hp2 - hp1) + lctPhi L st2.mem b F.n ≤
          lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + 20 ∧
        Ans st2.mem hp1 ∧ RerootRoots mem1 st2.mem b F u)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + Cq + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * A + Eq + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (dynLctWrapTail lp rh rA q) { mem := mem₀, regs := regs, pos := pos }
        (.returned hp') st' c ∧
      LctMemRep w h L P b F1 x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + Cq + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * A + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + Cq + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * A + 200 ∧
      Ans st'.mem hp ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  classical
  set logN := Nat.log 2 (F.n + 2) + 1 with hlogN
  set phi₀ := lctPhi L mem₀ b F.n with hphi₀
  have hlog_pos : 1 ≤ logN := by omega
  have hmul := wrap_mul3 (C_FINDROOT_OP L) Cq (C_CUT_OP L) logN
  have hhp_w : hp < 2 ^ w := by omega
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with ⟨harena_hp, _, hb_w, h36_w, _, _, _, hfn1_w, _⟩
  have hw1 : 1 < 2 ^ w := lt_trans (by decide) h36_w
  have hA_w : A < 2 ^ w := by omega
  have hhpA_w : hp + A < 2 ^ w := by omega
  have hu_w : u < 2 ^ w := by omega
  let regs1 := Function.update regs 20 (hp + A)
  have hs1 : Runs w p ω (.assign 20 (.bin .add (.reg rh) (.reg rA)))
      { mem := mem₀, regs := regs, pos := pos } .normal
      { mem := mem₀, regs := regs1, pos := pos } 4 :=
    runs_assign_iff.mpr ⟨hp + A, Expr.eval_add (Expr.eval_reg_of_eq hrh) (Expr.eval_reg_of_eq hrA)
      hhpA_w, rfl, rfl, rfl⟩
  have hfoot1 : ∀ a, lctFoot b x₀ a → a < hp + A := fun a ha =>
    lt_of_lt_of_le (hfoot a ha) (Nat.le_add_right _ _)
  have hz1 : ZeroFrom mem₀ (hp + A) := hz₀
  rw [← hmul] at hroom
  have hroom_fr : (hp + A) + phi₀ + C_FINDROOT_OP L * logN + 7000 * (L + 1) * (F.n + 2) + 2 <
      2 ^ w := by omega
  obtain ⟨hp1, st_fr, c1, x1, hrun_fr, hrep1, hresp1, hans_fr, hr_lt, hcanon1, _, hc1⟩ :=
    lctFindRootBody_runs (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hrep₀ hu hfoot1 hz1
      hroom_fr le_rfl ω
  set r := lctCanonRoot mem₀ b F.n u with hr_def
  let regs2 := Function.update regs1 21 hp1
  have hcall_fr : Runs w p ω (.call 21 lp.findRoot [.reg 0, .reg 1, .reg 20])
      { mem := mem₀, regs := regs1, pos := pos } .normal
      { mem := st_fr.mem, regs := regs2, pos := st_fr.pos } (3 + c1 + 1) := by
    refine runs_call_iff.mpr ⟨[b, u, hp + A], lctFindRootBody lp, .returned hp1, st_fr, c1,
      ?_, hfr_eq, hrun_fr, rfl, by cases st_fr; rfl, rfl⟩
    have h0 : regs1 0 = b := by simp [regs1, hr0]
    have h1 : regs1 1 = u := by simp [regs1, hr1]
    have h20 : regs1 20 = hp + A := by simp [regs1]
    simp [evalArgs, Expr.eval, h0, h1, h20]
  have hle1 : hp + A ≤ hp1 := hresp1.1
  let regs3 := Function.update regs2 22 r
  have hs3 : Runs w p ω (.assign 22 (.load (.reg 20)))
      { mem := st_fr.mem, regs := regs2, pos := st_fr.pos } .normal
      { mem := st_fr.mem, regs := regs3, pos := st_fr.pos } 3 := by
    refine runs_assign_iff.mpr ⟨r, Expr.eval_load_of_eq (Expr.eval_reg_of_eq ?_) hans_fr, rfl, rfl, rfl⟩
    simp [regs2, regs1]
  have hfoot2 : ∀ a, lctFoot b x1 a → a < hp1 := LctMemRep.foot_lt_of_respects hfoot1 hresp1
  have hz2 : ZeroFrom st_fr.mem hp1 := hresp1.2.2.1
  set phi1 := lctPhi L st_fr.mem b F.n with hphi1
  obtain ⟨hroom_q, hhp1A⟩ := wrap_room_q hroom hc1 hle1
  have hregs3_lo : ∀ i < 20, regs3 i = regs i := fun i hi => by
    simp [regs3, regs2, regs1, Function.update_of_ne (show i ≠ 22 by omega),
      Function.update_of_ne (show i ≠ 21 by omega), Function.update_of_ne (show i ≠ 20 by omega)]
  obtain ⟨hp2, st2, c2, x2, hrun_q, hrep2, hresp2, hc2, hans2, hroots2⟩ :=
    hq st_fr.mem x1 hp1 st_fr.pos regs3 hrep1 hfoot2 hz2 hle1 hroom_q hregs3_lo (by simp [regs3, regs2])
      (fun i hi => hresp1.2.2.2.1 (hp + i) (by omega) (fun hf => by have := hfoot _ hf; omega))
  have hle2 : hp1 ≤ hp2 := hresp2.1
  set phi2 := lctPhi L st2.mem b F.n with hphi2
  let regs4 := Function.update regs3 23 hp2
  have hhp2_w : hp2 + phi2 + C_CUT_OP L * logN + 7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w :=
    wrap_room_cut hroom hc1 hle1 hc2 hle2
  have hcp_args : ∀ a ∈ [hp1, hp, A], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hpre_cp : (copyWordsContract w).pre [hp1, hp, A] st2.mem :=
    ⟨hp1, hp, A, rfl, hw1, hhp1A, by omega, Or.inl hle1⟩
  obtain ⟨body_cp, hcp_eq, o_cp, st_cp, c_cp, hrun_cp, hpost_cp, hc_cp⟩ :=
    hp_base.copyWords_ok [hp1, hp, A] st2.mem st2.pos ω hcp_args hpre_cp
  obtain ⟨_, _, _, hcp_arg, _, hcp_vals, hcp_out⟩ := hpost_cp
  cases hcp_arg
  have hc_cp' : c_cp ≤ 17 * A + 10 := hc_cp
  let regs5 := Function.update regs4 25 o_cp.value
  have hcall_cp : Runs w p ω (.call 25 lp.copyWords [.reg 21, .reg rh, .reg rA])
      { mem := st2.mem, regs := regs4, pos := st2.pos } .normal
      { mem := st_cp.mem, regs := regs5, pos := st_cp.pos } (3 + c_cp + 1) := by
    refine runs_call_iff.mpr ⟨[hp1, hp, A], body_cp, o_cp, st_cp, c_cp, ?_, hcp_eq, hrun_cp,
      rfl, by cases st_cp; rfl, rfl⟩
    have h21 : regs4 21 = hp1 := by simp [regs4, regs3, regs2]
    have hrh4 : regs4 rh = hp := by
      simp [regs4, regs3, regs2, regs1, Function.update_of_ne (show rh ≠ 23 by omega),
        Function.update_of_ne (show rh ≠ 22 by omega), Function.update_of_ne (show rh ≠ 21 by omega),
        Function.update_of_ne (show rh ≠ 20 by omega), hrh]
    have hrA4 : regs4 rA = A := by
      simp [regs4, regs3, regs2, regs1, Function.update_of_ne (show rA ≠ 23 by omega),
        Function.update_of_ne (show rA ≠ 22 by omega), Function.update_of_ne (show rA ≠ 21 by omega),
        Function.update_of_ne (show rA ≠ 20 by omega), hrA]
    simp [evalArgs, Expr.eval, h21, hrh4, hrA4]
  have hfoot_x1 : ∀ a, lctFoot b x1 a → a < hp ∨ hp + A ≤ a := fun a ha => by
    rcases hresp1.2.2.2.2 a ha with h0 | ⟨h1, _⟩
    · exact Or.inl (hfoot a h0)
    · exact Or.inr h1
  have hfoot_x2 : ∀ a, lctFoot b x2 a → a < hp ∨ hp + A ≤ a := fun a ha => by
    rcases hresp2.2.2.2.2 a ha with h0 | ⟨h1, _⟩
    · exact hfoot_x1 a h0
    · exact Or.inr (le_trans hle1 h1)
  have hcp_keep : ∀ a, (a < hp ∨ hp + A ≤ a) → st_cp.mem a = st2.mem a := fun a ha => hcp_out a ha
  have hloc_cp := lctDSRep_local w h L P b F1 x2 st2.mem st_cp.mem
    (fun a ha => (hcp_keep a (hfoot_x2 a ha)).symm)
  have hrep_cp : LctMemRep w h L P b F1 x2 st_cp.mem := hloc_cp.1 hrep2
  have hx2n : x2.n = F.n := by rw [hrep2.2.2.2.2.1, hF1n]
  have hphi_cp : lctPhi L st_cp.mem b F.n = phi2 := by
    have := hloc_cp.2; simp only [lctDSRep, hx2n] at this; exact this.symm
  have hfoot_cp : ∀ a, lctFoot b x2 a → a < hp2 := LctMemRep.foot_lt_of_respects hfoot2 hresp2
  have hz_cp : ZeroFrom st_cp.mem hp2 := fun a ha =>
    (hcp_keep a (Or.inr (by omega))).trans (hresp2.2.2.1 a ha)
  have hroom_cut : hp2 + lctPhi L st_cp.mem b F1.n + C_CUT_OP L * (Nat.log 2 (F1.n + 2) + 1) +
      7000 * (L + 1) * (F1.n + 2) + 1 < 2 ^ w := by rw [hF1n, hphi_cp]; exact hhp2_w
  obtain ⟨hp3, st3, c3, x3, hrun_cut, hrep3, hresp3, hc3, hroots3⟩ :=
    lctCutBody_runs (x := r) (y := r) (pos := st_cp.pos) (space := lctPhi L st_cp.mem b F1.n +
      C_CUT_OP L * (Nat.log 2 (F1.n + 2) + 1) + 1) p lp st_cp.mem hp_base hp_sp hexpose_eq
      hreroot_eq hrep_cp hfoot_cp hz_cp hroom_cut le_rfl ω
  have hcut_self : F1.cut r r = F1 := cut_eq_self_of_bad_args hF1v (Or.inr (Or.inr rfl))
  rw [hcut_self] at hrep3 hc3
  rw [hF1n, hphi_cp] at hc3
  have hle3 : hp2 ≤ hp3 := hresp3.1
  let regs6 := Function.update regs5 24 hp3
  have hcall_cut : Runs w p ω (.call 24 lp.cut [.reg 0, .reg 22, .reg 22, .reg 23])
      { mem := st_cp.mem, regs := regs5, pos := st_cp.pos } .normal
      { mem := st3.mem, regs := regs6, pos := st3.pos } (4 + c3 + 1) := by
    refine runs_call_iff.mpr ⟨[b, r, r, hp2], lctCutBody lp, .returned hp3, st3, c3, ?_, hcut_eq,
      hrun_cut, rfl, by cases st3; rfl, rfl⟩
    have h0 : regs5 0 = b := by simp [regs5, regs4, regs3, regs2, regs1, hr0]
    have h22 : regs5 22 = r := by simp [regs5, regs4, regs3]
    have h23 : regs5 23 = hp2 := by simp [regs5, regs4]
    simp [evalArgs, Expr.eval, h0, h22, h23]
  obtain ⟨hhp3_w, hhp3_sp, hcost⟩ := wrap_budget hroom hc1 hle1 hc2 hle2 hc_cp' hc3 hle3
  have hs_ret : Runs w p ω (.ret (.reg 24)) { mem := st3.mem, regs := regs6, pos := st3.pos }
      (.returned hp3) { mem := st3.mem, regs := regs6, pos := st3.pos } 2 :=
    runs_ret_iff.mpr ⟨hp3, Expr.eval_reg_of_eq (by simp [regs6]), rfl, rfl, rfl⟩
  have hrun := runs_seq_normal hs1 (runs_seq_normal hcall_fr (runs_seq_normal hs3
    (runs_seq_normal hrun_q (runs_seq_normal hcall_cp (runs_seq_normal hcall_cut hs_ret)))))
  have hfoot_x3 : ∀ a, lctFoot b x3 a → lctFoot b x₀ a ∨ (hp ≤ a ∧ a < hp3) := fun a ha => by
    rcases hresp3.2.2.2.2 a ha with h2 | ⟨_, h3⟩
    · rcases hresp2.2.2.2.2 a h2 with h1 | ⟨h1a, _⟩
      · rcases hresp1.2.2.2.2 a h1 with h0 | ⟨h0a, _⟩
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h3⟩
  have hkeep_lo : ∀ a < hp, ¬ lctFoot b x₀ a → st3.mem a = mem₀ a := fun a ha hnf => by
    have hnf1 : ¬ lctFoot b x1 a := fun h1 => by
      rcases hresp1.2.2.2.2 a h1 with h0 | ⟨h0a, _⟩
      · exact hnf h0
      · omega
    have hnf2 : ¬ lctFoot b x2 a := fun h2 => by
      rcases hresp2.2.2.2.2 a h2 with h1 | ⟨h1a, _⟩
      · exact hnf1 h1
      · omega
    rw [hresp3.2.2.2.1 a (by omega) hnf2, hcp_keep a (Or.inl ha),
      hresp2.2.2.2.1 a (by omega) hnf1, hresp1.2.2.2.1 a (by omega) hnf]
  have hans_cp : Ans st_cp.mem hp := hAns _ _ _ _ hans2 (fun i hi => hcp_vals i hi)
  have hans3 : Ans st3.mem hp := by
    refine hAns _ _ _ _ hans_cp (fun i hi => ?_)
    have hnf2 : ¬ lctFoot b x2 (hp + i) := fun h2 => by
      rcases hfoot_x2 _ h2 with h | h <;> omega
    exact hresp3.2.2.2.1 _ (by omega) hnf2
  have harena_le : lctArenaHi b (lctCap F.n) ≤ hp := harena_hp
  have hcanon_cp : ∀ z, lctCanonRoot st_cp.mem b F.n z = lctCanonRoot st2.mem b F.n z := by
    intro z; unfold lctCanonRoot
    rw [show lctAuxParent st_cp.mem (lctNodesBase b) (lctCap F.n) =
        lctAuxParent st2.mem (lctNodesBase b) (lctCap F.n) from funext fun z =>
      lctAuxParent_agree (fun i _ hi => (hcp_keep i (Or.inl
        (lt_of_lt_of_le (by simpa [lctArenaHi] using hi) harena_le))).symm) z]
  have hroots : ∀ z < F.n, lctCanonRoot st3.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
    intro z hz
    have hr_n : r < F.n := hans_fr ▸ hr_lt
    have hc3 := (hroots3 z (by rw [hF1n]; exact hz)).2.1 (by rw [hF1n]; exact hr_n)
      (by rw [hF1n]; exact hr_n) hcut_self
    rw [hF1n] at hc3
    rw [hc3, hcanon_cp, hcanon_cp]
    have hq_z := hroots2 z hz
    have hq_r := hroots2 r hr_n
    have hru : F.SameComp r u := ((hrep₀.lctCanonRoot_spec hu).2.2.1).symm
    have hc1 : ∀ y, lctCanonRoot st_fr.mem b F.n y = lctCanonRoot mem₀ b F.n y := hcanon1
    simp only [hru, ↓reduceIte] at hq_r
    rw [hq_r, hq_z, hc1]
    by_cases hzu : F.SameComp z u
    · simp only [hzu, ↓reduceIte]
      exact ((hrep₀.lctCanonRoot_spec hu).2.2.2 z hz).2 hzu |>.symm
    · have hne : lctCanonRoot mem₀ b F.n z ≠ u := fun h => by
        apply hzu; have := (hrep₀.lctCanonRoot_spec hz).2.2.1; rw [h] at this; exact this
      simp only [hzu, hne, ↓reduceIte]
  refine ⟨hp3, _, _, x3, hrun, hrep3, ⟨by omega, ?_, hresp3.2.2.1, hkeep_lo, hfoot_x3⟩,
    ?_, hans3, hroots⟩
  · rw [← hmul]; exact hhp3_sp
  · rw [← hmul]; exact hcost

/-- Run of `dynLctWrapBody` when `regs rA = A` (`rA < 20`). -/
theorem dynLctWrapBody_runs {w h L P b u v hp A Cq Eq pos rh rA : ℕ}
    {F F1 : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (regs : ℕ → ℕ) (q : Stmt) (Ans : (ℕ → ℕ) → ℕ → Prop) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (hF1n : F1.n = F.n) (hF1v : F1.Valid) (hF1self : u = v → F1 = F)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hr0 : regs 0 = b) (hr1 : regs 1 = u) (hr2 : regs 2 = v) (hrh : regs rh = hp)
    (hrA : regs rA = A) (hrh20 : rh < 20) (hrA20 : rA < 20)
    (hAns : ∀ m m' a a', Ans m a → (∀ i < A, m' (a' + i) = m (a + i)) → Ans m' a')
    (hself : u = v → Ans mem₀ hp)
    (hq : u ≠ v → ∀ mem1 x1 hp1 pos1 regs1,
      LctMemRep w h L P b F x1 mem1 → (∀ a, lctFoot b x1 a → a < hp1) → ZeroFrom mem1 hp1 →
      hp + A ≤ hp1 →
      hp1 + lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) +
        Eq < 2 ^ w →
      (∀ i < 20, regs1 i = regs i) → regs1 21 = hp1 →
      (∀ i < A, mem1 (hp + i) = mem₀ (hp + i)) →
      ∃ (hp2 : ℕ) (st2 : State) (c2 : ℕ) (x2 : LctConc),
        Runs w p ω q { mem := mem1, regs := regs1, pos := pos1 } .normal
          { mem := st2.mem, regs := Function.update regs1 23 hp2, pos := st2.pos } c2 ∧
        LctMemRep w h L P b F1 x2 st2.mem ∧
        (lctDSRep w h L P).Respects (lctFoot b x1) hp1
          (lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + Eq) mem1 hp2 b x2 st2.mem ∧
        c2 + (hp2 - hp1) + lctPhi L st2.mem b F.n ≤
          lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + 20 ∧
        Ans st2.mem hp1 ∧ RerootRoots mem1 st2.mem b F u)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + Cq + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * A + Eq + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (dynLctWrapBody lp rh rA q) { mem := mem₀, regs := regs, pos := pos }
        (.returned hp') st' c ∧
      LctMemRep w h L P b F1 x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + Cq + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * A + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + Cq + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * A + 204 ∧
      Ans st'.mem hp ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  have hw1 : 1 < 2 ^ w := by
    have := hp_base.hh; have := hp_base.hw
    have h4 : 4 ≤ w := by omega
    exact lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h4)
  let st : State := { mem := mem₀, regs := regs, pos := pos }
  have hcond : Expr.eval w st (.bin .eq (.reg 1) (.reg 2)) = some (if u = v then 1 else 0) := by
    have hw' : (if u = v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simpa [BinOp.eval] using Expr.eval_bin (op := .eq)
      (Expr.eval_reg_of_eq hr1) (Expr.eval_reg_of_eq hr2) (by simpa [BinOp.eval] using hw')
  by_cases huv : u = v
  · subst huv
    rw [hF1self rfl]
    have hret : Runs w p ω (.ret (.reg rh)) st (.returned hp) st 2 :=
      runs_ret_iff.mpr ⟨hp, Expr.eval_reg_of_eq hrh, rfl, rfl, rfl⟩
    refine ⟨hp, st, 3 + 2 + 1, x₀, ?_, hrep₀,
      ⟨le_rfl, Nat.le_add_right _ _, hz₀, fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩,
      by dsimp only [st]; omega, hself rfl, fun _ _ => rfl⟩
    rw [dynLctWrapBody, runs_cond_iff]
    exact ⟨1, 2, by simpa using hcond, by simpa using hret, by decide⟩
  · have hu : u < F.n := (sameComp_lt_of_ne hV hsc huv).1
    obtain ⟨hp', st', c, x', hrun, hrep', hresp', hc, hans, hroots⟩ :=
      dynLctWrapTail_runs p lp mem₀ regs q Ans ω hp_base hp_sp hexpose_eq hreroot_eq hfr_eq hcut_eq
        hrep₀ hu hF1n hF1v hfoot (fun a ha => hz₀ a (by omega)) hr0 hr1 hrh hrA hrh20 hrA20
        hAns (hq huv) hroom
    refine ⟨hp', st', 3 + c + 1, x', ?_, hrep', hresp', by omega, hans, hroots⟩
    rw [dynLctWrapBody, runs_cond_iff]
    exact ⟨0, c, by simpa [huv] using hcond, by simpa using hrun, rfl⟩

/-- Run of `dynLctLinkWrap`. -/
theorem dynLctLinkWrap_runs {w h L P b a heap space pos : ℕ} {F : MathForest} {x₀ : LctConc}
    {e : ForestEdge} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hlink_eq : p.procs[lp.link]? = some (lctLinkBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : e.u < F.n) (hv : e.v < F.n) (hdisc : ¬ F.SameComp e.u e.v)
    (hfresh : ∀ e' ∈ F.edges, e'.eid ≠ e.eid) (heid : e.eid < 2 ^ w)
    (hfe : EdgeFits h L P e) (hedge : ForestEdgeAt mem₀ a h L P e) (ha : a + 3 + 4 * L ≤ heap)
    (hfoot : ∀ a, lctFoot b x₀ a → a < heap) (hz₀ : ZeroFrom mem₀ heap)
    (hroom : heap + lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) +
        7000 * (L + 1) * (F.n + 2) + 7 * L + 1 < 2 ^ w)
    (hspace : lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) + 7 * L + 1 ≤ space) :
    ∃ hp' st' c x',
      Runs w p ω (dynLctLinkWrap lp) (startState [b, a, heap] mem₀ pos) (.returned hp') st' c ∧
      LctMemRep w h L P b (F.link e) x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) heap space mem₀ hp' b x' st'.mem ∧
      c + (hp' - heap) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) + 80 ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z =
        if lctCanonRoot mem₀ b F.n z = lctCanonRoot mem₀ b F.n e.u then lctCanonRoot mem₀ b F.n e.v
        else lctCanonRoot mem₀ b F.n z := by
  obtain ⟨hlist, hcv, hcval, ⟨hfv, hfval⟩, ⟨hafv, hafval⟩, ⟨habv, habval⟩⟩ := hedge
  have hw_heap : heap < 2 ^ w := by omega
  have hb_lt_hp : b + LCT_HDR_L < heap := by
    rcases arenaHi_bounds hrep₀ hfoot hw_heap with ⟨har, -⟩
    have : b + LCT_HDR_L < lctArenaHi b (lctCap F.n) := by
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega
    omega
  have hmemL : mem₀ (b + LCT_HDR_L) = L := lctMemRep_hdrL hrep₀
  have hLCT3 : LCT_HDR_L < 2 ^ w := by
    have := hp_base.hh; have := hp_base.hw
    have h4 : 4 ≤ w := by omega
    have h16 := Nat.pow_le_pow_right (by decide : 0 < 2) h4
    unfold LCT_HDR_L; omega
  have h16w : 16 ≤ 2 ^ w := by
    have := hp_base.hh; have := hp_base.hw
    exact (by decide : 16 ≤ 2 ^ 4).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hbw : b + LCT_HDR_L < 2 ^ w := by omega
  have ha3 : a + 3 < 2 ^ w := by omega
  have ha3L1 : a + 3 + L < 2 ^ w := by omega
  have ha3L2 : a + 3 + 2 * L < 2 ^ w := by omega
  have ha3L3 : a + 3 + 3 * L < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha2 : a + 2 < 2 ^ w := by omega
  have e1 : a + (3 + L) = a + 3 + L := by omega
  have e2 : a + (3 + 2 * L) = a + 3 + 2 * L := by omega
  have e3 : a + (3 + 3 * L) = a + 3 + 3 * L := by omega
  obtain ⟨hpf, st₁, c, x', hrun, hrep', hresp, hc, hroots⟩ :=
    lctLinkBody_runs (cPtr := a + 3) (fPtr := a + 3 + L) (afPtr := a + 3 + 2 * L)
      (abPtr := a + 3 + 3 * L) (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hreroot_eq
      hrep₀ hu hv hdisc hfresh heid hfe hcv (by omega) hcval (e1 ▸ hfv) (by omega)
      (e1 ▸ hfval) (e2 ▸ hafv) (by omega) (e2 ▸ hafval) (e3 ▸ habv) (by omega) (e3 ▸ habval)
      hfoot hz₀ hroom hspace ω
  let st0 : State := startState [b, a, heap] mem₀ pos
  let r1 := Function.update st0.regs 10 L
  let r2 := Function.update r1 11 (a + 3)
  let r3 := Function.update r2 12 (a + 3 + L)
  let r4 := Function.update r3 13 (a + 3 + 2 * L)
  let r5 := Function.update r4 14 (a + 3 + 3 * L)
  have hs1 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))))
      st0 .normal { st0 with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨L, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_const hLCT3) hbw) hmemL, rfl, rfl, rfl⟩
  have hr1a : r1 1 = a := by simp [r1, st0, startState, Function.update_of_ne]
  have hs2 : Runs w p ω (.assign 11 (.bin .add (.reg 1) (.const 3)))
      { st0 with regs := r1 } .normal { st0 with regs := r2 } 4 :=
    runs_assign_iff.mpr ⟨a + 3, Expr.eval_add (Expr.eval_reg_of_eq hr1a)
      (Expr.eval_const (by omega)) ha3, rfl, rfl, rfl⟩
  have hs3 : Runs w p ω (.assign 12 (.bin .add (.reg 11) (.reg 10)))
      { st0 with regs := r2 } .normal { st0 with regs := r3 } 4 :=
    runs_assign_iff.mpr ⟨a + 3 + L, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
      (Expr.eval_reg_of_eq (by simp [r2, r1, Function.update_of_ne])) ha3L1, rfl, rfl, rfl⟩
  have hs4 : Runs w p ω (.assign 13 (.bin .add (.reg 12) (.reg 10)))
      { st0 with regs := r3 } .normal { st0 with regs := r4 } 4 :=
    runs_assign_iff.mpr ⟨a + 3 + 2 * L, by
      rw [show a + 3 + 2 * L = a + 3 + L + L by omega]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3]))
        (Expr.eval_reg_of_eq (by simp [r3, r2, r1, Function.update_of_ne])) (by omega),
      rfl, rfl, rfl⟩
  have hs5 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 10)))
      { st0 with regs := r4 } .normal { st0 with regs := r5 } 4 :=
    runs_assign_iff.mpr ⟨a + 3 + 3 * L, by
      rw [show a + 3 + 3 * L = a + 3 + 2 * L + L by omega]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]))
        (Expr.eval_reg_of_eq (by simp [r4, r3, r2, r1, Function.update_of_ne])) (by omega),
      rfl, rfl, rfl⟩
  let stBody : State := { st0 with regs := r5 }
  have hr5_0 : r5 0 = b := by simp [r5, r4, r3, r2, r1, st0, startState, Function.update_of_ne]
  have hr5_1 : r5 1 = a := by simp [r5, r4, r3, r2, r1, st0, startState, Function.update_of_ne]
  have hr5_2 : r5 2 = heap := by simp [r5, r4, r3, r2, r1, st0, startState, Function.update_of_ne]
  have hr5_11 : r5 11 = a + 3 := by simp [r5, r4, r3, r2, Function.update_of_ne]
  have hr5_12 : r5 12 = a + 3 + L := by simp [r5, r4, r3, Function.update_of_ne]
  have hr5_13 : r5 13 = a + 3 + 2 * L := by simp [r5, r4, Function.update_of_ne]
  have hr5_14 : r5 14 = a + 3 + 3 * L := by simp [r5]
  have hl0 : Expr.eval w stBody (.load (.reg 1)) = some e.eid :=
    Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr5_1) (by simpa [stBody, st0, startState] using hlist 0 (by simp))
  have hl1 : Expr.eval w stBody (.load (.bin .add (.reg 1) (.const 1))) = some e.u :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr5_1) (Expr.eval_const (by omega)) ha1)
      (by simpa [stBody, st0, startState] using hlist 1 (by simp))
  have hl2 : Expr.eval w stBody (.load (.bin .add (.reg 1) (.const 2))) = some e.v :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr5_1) (Expr.eval_const (by omega)) ha2)
      (by simpa [stBody, st0, startState] using hlist 2 (by simp))
  let st₂ : State := { st₁ with regs := Function.update r5 3 hpf }
  let linkArgs : List Expr :=
    [.reg 0, .load (.bin .add (.reg 1) (.const 1)),
     .load (.bin .add (.reg 1) (.const 2)), .load (.reg 1),
     .reg 11, .reg 12, .reg 13, .reg 14, .reg 2]
  have hcall : Runs w p ω (.call 3 lp.link linkArgs) stBody .normal st₂ (argsSize linkArgs + c + 1) := by
    refine runs_call_iff.mpr ⟨[b, e.u, e.v, e.eid, a + 3, a + 3 + L, a + 3 + 2 * L, a + 3 + 3 * L, heap],
      lctLinkBody lp, .returned hpf, st₁, c, ?_, hlink_eq, hrun, rfl, rfl, rfl⟩
    simp only [linkArgs, evalArgs, hl0, hl1, hl2]
    simp only [Expr.eval, stBody, hr5_0, hr5_2, hr5_11, hr5_12, hr5_13, hr5_14]
  have hcall_sz : argsSize linkArgs ≤ 40 := by simp [linkArgs, argsSize, Expr.size]
  have hret : Runs w p ω (.ret (.reg 3)) st₂ (.returned hpf) st₂ 2 :=
    runs_ret_iff.mpr ⟨hpf, Expr.eval_reg_of_eq (by simp [st₂]), rfl, rfl, rfl⟩
  have hseq := runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3
    (runs_seq_normal hs4 (runs_seq_normal hs5 (runs_seq_normal hcall hret)))))
  refine ⟨hpf, st₂, _, x', hseq, hrep', hresp, ?_, hroots⟩
  dsimp only [st₂]
  have hln : (F.link e).n = F.n := rfl
  rw [hln] at hc
  omega

/-- Run of `dynLctPathMinWrap`. -/
theorem dynLctPathMinWrap_runs {w h L P b u v hp pos : ℕ} {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hq_eq : p.procs[lp.pathMin]? = some (lctPathMinBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * (2 * L + 4) + (2 * L + 5) + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (dynLctPathMinWrap lp) (startState [b, u, v, hp] mem₀ pos)
        (.returned hp') st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * (2 * L + 4) + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * (2 * L + 4) + 220 ∧
      PathHitAt st'.mem hp h L P (F.pathMin u v) ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  have hhp_w : hp < 2 ^ w := by omega
  have hb_lt : b + LCT_HDR_L < hp := by
    rcases arenaHi_bounds hrep₀ hfoot hhp_w with ⟨har, -⟩
    have : b + LCT_HDR_L < lctArenaHi b (lctCap F.n) := by
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega
    omega
  have h16w : 16 ≤ 2 ^ w := by
    have := hp_base.hh; have := hp_base.hw
    exact (by decide : 16 ≤ 2 ^ 4).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hmemL : mem₀ (b + LCT_HDR_L) = L := lctMemRep_hdrL hrep₀
  let st : State := startState [b, u, v, hp] mem₀ pos
  let r1 := Function.update st.regs 18 L
  let r2 := Function.update r1 19 (2 * L + 4)
  have hbw : b + LCT_HDR_L < 2 ^ w := by omega
  have h2Lw : 2 * L < 2 ^ w := by omega
  have h2L4w : 2 * L + 4 < 2 ^ w := by omega
  have hs1 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))))
      st .normal { st with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨L, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st, startState]))
      (Expr.eval_const (by unfold LCT_HDR_L; omega)) hbw) hmemL, rfl, rfl, rfl⟩
  have hs2 : Runs w p ω (.assign 19 (.bin .add (.bin .mul (.const 2) (.reg 18)) (.const 4)))
      { st with regs := r1 } .normal { st with regs := r2 } 6 :=
    runs_assign_iff.mpr ⟨2 * L + 4, Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq (by simp [r1])) h2Lw) (Expr.eval_const (by omega)) h2L4w, rfl, rfl, rfl⟩
  obtain ⟨hp', st', c, x', hrun, hrep', hresp', hc, hans, hroots⟩ :=
    dynLctWrapBody_runs (Cq := C_PATHMIN_OP L) (Eq := 2 * L + 5) (rh := 3) (rA := 19)
      p lp mem₀ r2 (.call 23 lp.pathMin [.reg 0, .reg 1, .reg 2, .reg 21])
      (fun m a => PathHitAt m a h L P (F.pathMin u v)) ω hp_base hp_sp
      hexpose_eq hreroot_eq hfr_eq hcut_eq hrep₀ hV hsc rfl hV (fun _ => rfl) hfoot hz₀
      (by simp [r2, r1, st, startState, Function.update_of_ne])
      (by simp [r2, r1, st, startState, Function.update_of_ne])
      (by simp [r2, r1, st, startState, Function.update_of_ne])
      (by simp [r2, r1, st, startState, Function.update_of_ne])
      (by simp [r2]) (by decide) (by decide)
      (fun _ _ _ _ hm hag => pathHitAt_shift hm hag)
      (fun huv => by subst huv; rw [pathMin_self]; exact hz₀ hp le_rfl)
      (by
        intro huv mem1 x1 hp1 pos1 regs1 hrep1 hfoot1 hz1 _ hroom1 hregs1 hr21 _
        have hv := sameComp_lt_of_ne hV hsc huv
        obtain ⟨hp2, st2, c2, x2, hrun2, hrep2, hresp2, hans2, hc2, hroots2⟩ :=
          lctPathMinBody_runs (pos := pos1)
            (space := lctPhi L mem1 b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) + (2 * L + 5))
            p lp mem1 hp_base hp_sp hexpose_eq hreroot_eq hrep1 hv.1 hv.2 hsc hfoot1 hz1
            (by omega) (by omega) ω
        refine ⟨hp2, st2, 4 + c2 + 1, x2, ?_, hrep2, hresp2, by omega,
          pathHitAt_of_lctPathMinAt (r := F.pathMin u v) hans2, hroots2 huv⟩
        refine runs_call_iff.mpr ⟨[b, u, v, hp1], lctPathMinBody lp, .returned hp2, st2, c2, ?_, hq_eq,
          hrun2, rfl, by cases st2; rfl, rfl⟩
        have h0 : regs1 0 = b := (hregs1 0 (by decide)).trans (by simp [r2, r1, st, startState, Function.update_of_ne])
        have h1 : regs1 1 = u := (hregs1 1 (by decide)).trans (by simp [r2, r1, st, startState, Function.update_of_ne])
        have h2 : regs1 2 = v := (hregs1 2 (by decide)).trans (by simp [r2, r1, st, startState, Function.update_of_ne])
        simp [evalArgs, Expr.eval, h0, h1, h2, hr21]) hroom
  refine ⟨hp', st', 5 + (6 + c + 1) + 1, x', runs_seq_normal hs1 (runs_seq_normal hs2 hrun),
    hrep', hresp', by omega, hans, hroots⟩

/-- Run of `dynLctPathSumWrap`. -/
theorem dynLctPathSumWrap_runs {w h L P b u v hp pos : ℕ} {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hq_eq : p.procs[lp.pathSum]? = some (lctPathSumBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (hfits : Fits h L (F.pathSum u v))
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * L + (L + 1) + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (dynLctPathSumWrap lp) (startState [b, u, v, hp] mem₀ pos)
        (.returned hp') st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + 215 ∧
      (Valid st'.mem hp h L ∧ intVal st'.mem hp h L = F.pathSum u v) ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  have hhp_w : hp < 2 ^ w := by omega
  have hb_lt : b + LCT_HDR_L < hp := by
    rcases arenaHi_bounds hrep₀ hfoot hhp_w with ⟨har, -⟩
    have : b + LCT_HDR_L < lctArenaHi b (lctCap F.n) := by
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega
    omega
  have h16w : 16 ≤ 2 ^ w := by
    have := hp_base.hh; have := hp_base.hw
    exact (by decide : 16 ≤ 2 ^ 4).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hmemL : mem₀ (b + LCT_HDR_L) = L := lctMemRep_hdrL hrep₀
  let st : State := startState [b, u, v, hp] mem₀ pos
  let r1 := Function.update st.regs 19 L
  have hbw : b + LCT_HDR_L < 2 ^ w := by omega
  have hs1 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))))
      st .normal { st with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨L, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st, startState]))
      (Expr.eval_const (by unfold LCT_HDR_L; omega)) hbw) hmemL, rfl, rfl, rfl⟩
  obtain ⟨hp', st', c, x', hrun, hrep', hresp', hc, hans, hroots⟩ :=
    dynLctWrapBody_runs (Cq := C_PATHSUM_OP L) (Eq := L + 1) (rh := 3) (rA := 19)
      p lp mem₀ r1 (.call 23 lp.pathSum [.reg 0, .reg 1, .reg 2, .reg 21])
      (fun m a => Valid m a h L ∧ intVal m a h L = F.pathSum u v) ω hp_base hp_sp
      hexpose_eq hreroot_eq hfr_eq hcut_eq hrep₀ hV hsc rfl hV (fun _ => rfl) hfoot hz₀
      (by simp [r1, st, startState, Function.update_of_ne])
      (by simp [r1, st, startState, Function.update_of_ne])
      (by simp [r1, st, startState, Function.update_of_ne])
      (by simp [r1, st, startState, Function.update_of_ne])
      (by simp [r1]) (by decide) (by decide)
      (fun _ _ _ _ hm hag => sumAt_shift hm hag)
      (fun huv => by subst huv; rw [pathSum_self]; exact ⟨zeroFrom_valid hz₀ le_rfl, intVal_zeroFrom hz₀ le_rfl⟩)
      (by
        intro huv mem1 x1 hp1 pos1 regs1 hrep1 hfoot1 hz1 _ hroom1 hregs1 hr21 _
        have hv := sameComp_lt_of_ne hV hsc huv
        obtain ⟨hp2, st2, c2, x2, hrun2, hrep2, hresp2, hvalid2, hval2, hc2, hroots2⟩ :=
          lctPathSumBody_runs (pos := pos1)
            (space := lctPhi L mem1 b F.n + C_PATHSUM_OP L * (Nat.log 2 (F.n + 2) + 1) + (L + 1))
            p lp mem1 hp_base hp_sp hexpose_eq hreroot_eq hrep1 hv.1 hv.2 hsc hfoot1 hz1
            (by omega) (by omega) ω
        refine ⟨hp2, st2, 4 + c2 + 1, x2, ?_, hrep2, hresp2, by omega,
          ⟨hvalid2, hval2.trans (wrap_of_fits hfits)⟩, hroots2⟩
        refine runs_call_iff.mpr ⟨[b, u, v, hp1], lctPathSumBody lp, .returned hp2, st2, c2, ?_, hq_eq,
          hrun2, rfl, by cases st2; rfl, rfl⟩
        have h0 : regs1 0 = b := (hregs1 0 (by decide)).trans (by simp [r1, st, startState, Function.update_of_ne])
        have h1 : regs1 1 = u := (hregs1 1 (by decide)).trans (by simp [r1, st, startState, Function.update_of_ne])
        have h2 : regs1 2 = v := (hregs1 2 (by decide)).trans (by simp [r1, st, startState, Function.update_of_ne])
        simp [evalArgs, Expr.eval, h0, h1, h2, hr21]) hroom
  refine ⟨hp', st', 5 + c + 1, x', runs_seq_normal hs1 hrun, hrep', hresp', by omega, hans, hroots⟩

/-- Run of `dynLctPathAddWrap`. -/
theorem dynLctPathAddWrap_runs {w h L P b u v a hp pos : ℕ} {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hq_eq : p.procs[lp.pathAdd]? = some (lctPathAddBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (ha : a + L ≤ hp) (hva : Valid mem₀ a h L)
    (hfit : ∀ e ∈ (F.pathAdd u v (readRat mem₀ a h L P)).edges, EdgeFits h L P e)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * L + (L + 1) + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (dynLctPathAddWrap lp) (startState [b, u, v, a, hp] mem₀ pos)
        (.returned hp') st' c ∧
      LctMemRep w h L P b (F.pathAdd u v (readRat mem₀ a h L P)) x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + (17 * L + 250) ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  let st : State := startState [b, u, v, a, hp] mem₀ pos
  have h16w : 16 ≤ 2 ^ w := by
    have := hp_base.hh; have := hp_base.hw
    have h4 : 4 ≤ w := by omega
    exact (by decide : 16 ≤ 2 ^ 4).trans (Nat.pow_le_pow_right (by decide : 0 < 2) h4)
  have hw1 : 1 < 2 ^ w := by omega
  have hhp_w : hp < 2 ^ w := by omega
  have hL_w : L < 2 ^ w := hp_base.hL
  have hcond_eq : Expr.eval w st (.bin .eq (.reg 1) (.reg 2)) = some (if u = v then 1 else 0) := by
    have hw' : (if u = v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simpa [BinOp.eval] using Expr.eval_bin (op := .eq)
      (Expr.eval_reg_of_eq (w := w) (st := st) (v := u) rfl)
      (Expr.eval_reg_of_eq (w := w) (st := st) (v := v) rfl) (by simpa [BinOp.eval] using hw')
  by_cases huv : u = v
  · subst huv
    rw [pathAdd_self]
    have hret : Runs w p ω (.ret (.reg 4)) st (.returned hp) st 2 :=
      runs_ret_iff.mpr ⟨hp, Expr.eval_reg_of_eq (w := w) (st := st) rfl, rfl, rfl, rfl⟩
    refine ⟨hp, st, 3 + 2 + 1, x₀, ?_, hrep₀,
      ⟨le_rfl, Nat.le_add_right _ _, hz₀, fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩,
      by dsimp only [st, startState]; omega, fun _ _ => rfl⟩
    rw [dynLctPathAddWrap, runs_cond_iff]
    exact ⟨1, 2, by simpa using hcond_eq, by simpa using hret, by decide⟩
  have hu := (sameComp_lt_of_ne hV hsc huv).1
  have hv := (sameComp_lt_of_ne hV hsc huv).2
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with ⟨harena_le, -⟩
  have hmemL : mem₀ (b + LCT_HDR_L) = L := lctMemRep_hdrL hrep₀
  have hbw : b + LCT_HDR_L < 2 ^ w := by
    have : b + LCT_HDR_L < lctArenaHi b (lctCap F.n) := by
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega
    omega
  let r1 := Function.update st.regs 19 L
  have hs_ld : Runs w p ω (.assign 19 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))))
      st .normal { st with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨L, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st, startState]))
      (Expr.eval_const (by unfold LCT_HDR_L; omega)) hbw) hmemL, rfl, rfl, rfl⟩
  have hcp_args : ∀ x ∈ [a, hp, L], x < 2 ^ w := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  have hpre_cp : (copyWordsContract w).pre [a, hp, L] mem₀ :=
    ⟨a, hp, L, rfl, hw1, by omega, by omega, Or.inr ha⟩
  obtain ⟨body_cp, hcp_eq, o_cp, st_cp, c_cp, hrun_cp, hpost_cp, hc_cp⟩ :=
    hp_base.copyWords_ok [a, hp, L] mem₀ pos ω hcp_args hpre_cp
  obtain ⟨_, _, _, hcp_arg, _, hcp_vals, hcp_out⟩ := hpost_cp
  cases hcp_arg
  have hc_cp' : c_cp ≤ 17 * L + 10 := hc_cp
  let regs' := Function.update r1 26 o_cp.value
  have hcall_cp : Runs w p ω (.call 26 lp.copyWords [.reg 3, .reg 4, .reg 19])
      { st with regs := r1 } .normal
      { mem := st_cp.mem, regs := regs', pos := st_cp.pos } (3 + c_cp + 1) := by
    refine runs_call_iff.mpr ⟨[a, hp, L], body_cp, o_cp, st_cp, c_cp, ?_, hcp_eq, hrun_cp,
      rfl, by cases st_cp; rfl, rfl⟩
    simp [evalArgs, Expr.eval, r1, st, startState, Function.update_of_ne]
  have hkeep : ∀ x, x < hp → st_cp.mem x = mem₀ x := fun x hx => hcp_out x (Or.inl hx)
  have hloc := lctDSRep_local w h L P b F x₀ mem₀ st_cp.mem (fun x hx => (hkeep x (hfoot x hx)).symm)
  have hrep_cp : LctMemRep w h L P b F x₀ st_cp.mem := hloc.1 hrep₀
  have hphi_cp : lctPhi L st_cp.mem b F.n = lctPhi L mem₀ b F.n := by
    have h2 := hloc.2; simp only [lctDSRep, hrep₀.2.2.2.2.1] at h2; exact h2.symm
  have hz_cp : ZeroFrom st_cp.mem (hp + L) := fun x hx =>
    (hcp_out x (Or.inr hx)).trans (hz₀ x (by omega))
  have hcanon_cp : ∀ z, lctCanonRoot st_cp.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
    intro z; unfold lctCanonRoot
    rw [show lctAuxParent st_cp.mem (lctNodesBase b) (lctCap F.n) =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n) from funext fun z =>
      lctAuxParent_agree (fun i _ hi => (hkeep i
        (lt_of_lt_of_le (by simpa [lctArenaHi] using hi) harena_le)).symm) z]
  have hr0' : regs' 0 = b := by simp [regs', r1, st, startState, Function.update_of_ne]
  have hr1' : regs' 1 = u := by simp [regs', r1, st, startState, Function.update_of_ne]
  have hr2' : regs' 2 = v := by simp [regs', r1, st, startState, Function.update_of_ne]
  have hr4' : regs' 4 = hp := by simp [regs', r1, st, startState, Function.update_of_ne]
  have hr19' : regs' 19 = L := by simp [regs', r1, Function.update_of_ne]
  have hroom' : hp + lctPhi L st_cp.mem b F.n +
      (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * L + (L + 1) + 200 < 2 ^ w := by rw [hphi_cp]; exact hroom
  obtain ⟨hp', st', c, x', hrun, hrep', hresp', hc, -, hroots⟩ :=
    dynLctWrapTail_runs (A := L) (Cq := C_PATHADD_OP L) (Eq := L + 1) (rh := 4) (rA := 19)
      (F1 := F.pathAdd u v (readRat mem₀ a h L P)) (pos := st_cp.pos) p lp st_cp.mem regs'
      (.call 23 lp.pathAdd [.reg 0, .reg 1, .reg 2, .reg 4, .const 0, .reg 21])
      (fun _ _ => True) ω hp_base hp_sp hexpose_eq hreroot_eq hfr_eq hcut_eq hrep_cp hu
      (pathAdd_n _ _ _ _) (MathForest.pathAdd_valid hV _ _ _) hfoot hz_cp hr0' hr1' hr4' hr19'
      (by decide) (by decide) (fun _ _ _ _ _ _ => trivial)
      (by
          intro mem1 x1 hp1 pos1 regs1 hrep1 hfoot1 hz1 hle hroom1 hregs1 hr21 hag
          have hag' : ∀ i < L, mem1 (hp + i) = mem₀ (a + i) := fun i hi =>
            (hag i hi).trans (hcp_vals i hi)
          have hvalid1 : Valid mem1 hp h L := fun i hi => by rw [hag' i hi]; exact hva i hi
          have hδ : ((if (0 : ℕ) = 0 then intVal mem1 hp h L else -intVal mem1 hp h L : ℤ) : ℚ) /
              (2 : ℚ) ^ P = readRat mem₀ a h L P := by
            simp only [↓reduceIte]; unfold readRat; rw [intVal_congr hag']
          obtain ⟨hp2, st2, c2, x2, hrun2, hrep2, hresp2, hc2, hroots2⟩ :=
            lctPathAddBody_runs (dPtr := hp) (dNeg := 0) (pos := pos1)
              (space := lctPhi L mem1 b F.n + C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) + (L + 1))
              p lp mem1 hp_base hp_sp hexpose_eq hreroot_eq hrep1 hu hv hsc (by decide) hvalid1
              (by omega) hδ hfit hfoot1 hz1 (by omega) (by omega) ω
          rw [pathAdd_n] at hc2
          refine ⟨hp2, st2, 6 + c2 + 1, x2, ?_, hrep2, hresp2, by omega, trivial, hroots2 huv⟩
          refine runs_call_iff.mpr ⟨[b, u, v, hp, 0, hp1], lctPathAddBody lp, .returned hp2, st2, c2,
            ?_, hq_eq, hrun2, rfl, by cases st2; rfl, rfl⟩
          have h0 : regs1 0 = b := (hregs1 0 (by decide)).trans hr0'
          have h1 : regs1 1 = u := (hregs1 1 (by decide)).trans hr1'
          have h2 : regs1 2 = v := (hregs1 2 (by decide)).trans hr2'
          have h4 : regs1 4 = hp := (hregs1 4 (by decide)).trans hr4'
          have h0w : 0 < 2 ^ w := by omega
          simp [evalArgs, Expr.eval, h0, h1, h2, h4, hr21, h0w]) hroom'
  refine ⟨hp', st', 3 + (5 + ((3 + c_cp + 1) + c + 1) + 1) + 1, x', ?_, hrep', ?_, ?_, ?_⟩
  · rw [dynLctPathAddWrap, runs_cond_iff]
    refine ⟨0, _, by simpa [huv] using hcond_eq, ?_, rfl⟩
    simp only [↓reduceIte]
    exact runs_seq_normal hs_ld (runs_seq_normal hcall_cp hrun)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hresp'
    refine ⟨h1, by rw [← hphi_cp]; exact h2, h3, fun x hx hnf => ?_, h5⟩
    rw [h4 x hx hnf, hkeep x hx]
  · rw [hphi_cp] at hc; omega
  · intro z hz; rw [hroots z hz, hcanon_cp]

end DynamicWrapRun

section Implements

private theorem dyn_xl_le {X L lg LG : ℕ} (hX : X ≤ 930000 * (L + 1)) (hlg : lg ≤ LG) :
    X * lg ≤ 1000000 * (L + 1) * LG :=
  Nat.mul_le_mul (le_trans hX (by omega)) hlg

private theorem dyn_cF (L : ℕ) : C_FINDROOT_OP L ≤ 930000 * (L + 1) := by unfold C_FINDROOT_OP; omega
private theorem dyn_cL (L : ℕ) : C_LINK_OP L ≤ 930000 * (L + 1) := by unfold C_LINK_OP; omega
private theorem dyn_cC (L : ℕ) : C_CUT_OP L ≤ 930000 * (L + 1) := by unfold C_CUT_OP; omega
private theorem dyn_cPA (L : ℕ) : C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L ≤ 930000 * (L + 1) := by unfold C_FINDROOT_OP C_PATHADD_OP C_CUT_OP; omega
private theorem dyn_cPM (L : ℕ) : C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L ≤ 930000 * (L + 1) := by unfold C_FINDROOT_OP C_PATHMIN_OP C_CUT_OP; omega
private theorem dyn_cPS (L : ℕ) : C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L ≤ 930000 * (L + 1) := by unfold C_FINDROOT_OP C_PATHSUM_OP C_CUT_OP; omega
private theorem dyn_eS (L k : ℕ) (hk : k ≤ 1000) : k ≤ 100 * L + 1000 := by omega
private theorem dyn_eS2 (L : ℕ) : 7 * L + 1 ≤ 100 * L + 1000 := by omega
private theorem dyn_eS3 (L : ℕ) : 18 * L + (L + 1) + 200 ≤ 100 * L + 1000 := by omega
private theorem dyn_eS4 (L : ℕ) : 18 * (2 * L + 4) + (2 * L + 5) + 200 ≤ 100 * L + 1000 := by omega
private theorem dyn_fit1 {hp phi PhiN XL M MN e L A W : ℕ} (hphi : phi ≤ PhiN) (hXL : XL ≤ A)
    (hM : M ≤ MN) (he : e ≤ 100 * L + 1000) (hroom : hp + (PhiN + A + MN + 100 * L + 1000) < W) :
    hp + phi + XL + M + e < W ∧ phi + XL + e ≤ PhiN + A + MN + 100 * L + 1000 := by omega
private theorem dyn_fit2 {hp phi PhiN XL M MN e1 e2 L A W : ℕ} (hphi : phi ≤ PhiN) (hXL : XL ≤ A)
    (hM : M ≤ MN) (he : e1 + e2 ≤ 100 * L + 1000) (hroom : hp + (PhiN + A + MN + 100 * L + 1000) < W) :
    hp + phi + XL + M + e1 + e2 < W ∧ phi + XL + e1 + e2 ≤ PhiN + A + MN + 100 * L + 1000 := by omega
private theorem dyn_fit3 {hp phi PhiN XL M MN e1 e2 e3 L A W : ℕ} (hphi : phi ≤ PhiN) (hXL : XL ≤ A)
    (hM : M ≤ MN) (he : e1 + e2 + e3 ≤ 100 * L + 1000) (hroom : hp + (PhiN + A + MN + 100 * L + 1000) < W) :
    hp + phi + XL + M + e1 + e2 + e3 < W ∧ phi + XL + e1 + e3 ≤ PhiN + A + MN + 100 * L + 1000 := by omega
private theorem dyn_rate_split {X e L lg : ℕ} (hlg : 1 ≤ lg) (hX : X ≤ 930000 * (L + 1))
    (he : e ≤ 70000 * (L + 1)) : X * lg + e ≤ 1000000 * (L + 1) * lg := by
  have h1 : X * lg ≤ 930000 * (L + 1) * lg := Nat.mul_le_mul_right _ hX
  have h2 : 70000 * (L + 1) ≤ 70000 * (L + 1) * lg := Nat.le_mul_of_pos_right _ hlg
  have h3 : 930000 * ((L + 1) * lg) + 70000 * ((L + 1) * lg) = 1000000 * ((L + 1) * lg) := by
    rw [← Nat.add_mul]
  calc X * lg + e ≤ 930000 * (L + 1) * lg + 70000 * (L + 1) := Nat.add_le_add h1 he
    _ ≤ 930000 * (L + 1) * lg + 70000 * (L + 1) * lg := Nat.add_le_add_left h2 _
    _ = 930000 * ((L + 1) * lg) + 70000 * ((L + 1) * lg) := by simp only [Nat.mul_assoc]
    _ = 1000000 * ((L + 1) * lg) := h3
    _ = 1000000 * (L + 1) * lg := (Nat.mul_assoc _ _ _).symm
private theorem dyn_cost1 {c d phi' phi X lg e L : ℕ} (hc : c + d + phi' ≤ phi + X * lg + e)
    (hlg : 1 ≤ lg) (hX : X ≤ 930000 * (L + 1)) (he : e ≤ 70000 * (L + 1)) :
    c + phi' ≤ 1000000 * (L + 1) * lg + phi := by
  calc c + phi' ≤ phi + (X * lg + e) :=
        (Nat.add_le_add_right (Nat.le_add_right c d) phi').trans (by simpa [Nat.add_assoc] using hc)
    _ ≤ phi + 1000000 * (L + 1) * lg := Nat.add_le_add_left (dyn_rate_split hlg hX he) phi
    _ = 1000000 * (L + 1) * lg + phi := Nat.add_comm _ _
private theorem dyn_cost0 {c d phi' phi X lg L : ℕ} (hc : c + d + phi' ≤ phi + X * lg)
    (hlg : 1 ≤ lg) (hX : X ≤ 930000 * (L + 1)) : c + phi' ≤ 1000000 * (L + 1) * lg + phi :=
  dyn_cost1 (e := 0) (by simpa using hc) hlg hX (Nat.zero_le _)
private theorem dyn_cost2 {c d phi' phi X lg e1 e2 L : ℕ}
    (hc : c + d + phi' ≤ phi + X * lg + e1 + e2) (hlg : 1 ≤ lg)
    (hX : X ≤ 930000 * (L + 1)) (he : e1 + e2 ≤ 70000 * (L + 1)) :
    c + phi' ≤ 1000000 * (L + 1) * lg + phi :=
  dyn_cost1 (by simpa [Nat.add_assoc] using hc) hlg hX he

/-- For every `0 < h`, `2 * h + 2 ≤ w`, and `L, P < 2 ^ w`, a program containing the fixed
module `dynLctForestBodies h b0` implements `forestMachineContract lctForestModel w h L P
(lctForestRate L) (lctForestAlloc w L N)` at `b0`, `lctForestOp b0`. -/
theorem dynLctForest_implements {w h L P N b0 : ℕ} {p : Program} (hh : 0 < h)
    (hw : 2 * h + 2 ≤ w) (hL : L < 2 ^ w) (hP : P < 2 ^ w)
    (hp : p.HasAt b0 (dynLctForestBodies h b0)) :
    (lctForestRep w h L P N).Implements w p b0 (lctForestOp b0)
      (forestMachineContract lctForestModel w h L P (lctForestRate L) (lctForestAlloc w L N)) := by
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hp5⟩ := dynLctForestBodies_procs hp
  have hbase := dynLctBaseOk hh hw hL hP hp5
  have hsp : ∃ spB, (LctProcs.atBase (b0 + 5)).splay = SplayProcs.atBase spB := ⟨b0 + 5 + 11, rfl⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -, -, h9, h10⟩ := lctBodies_procs hp5
  refine ⟨lctForestRep_local w h L P N, ?_, ?_⟩
  · intro args mem pos ω _ hpre hz hroom
    obtain ⟨n, heap, rfl⟩ := hpre
    have hroom' : heap + lctForestAlloc w L N 6 [n, L, P, heap] < 2 ^ w := hroom
    by_cases hnN : n ≤ N
    swap
    · simp [lctForestAlloc, hnN] at hroom'
    simp only [lctForestAlloc, ↓reduceIte, List.getD_cons_zero, hnN] at hroom'
    obtain ⟨hp', st', c, x, hrun, hrep, hresp, hc⟩ :=
      dynLctInitWrap_runs (n := n) (heap := heap) (pos := pos) p (LctProcs.atBase (b0 + 5)) mem hh hw hL hP h0 hz
        (by omega) ω
    have hxn : x.n = n := hrep.2.2.2.2.1
    refine ⟨_, hw0, .returned hp', st', c, hrun, (MathForest.empty n, rootsOn n id), x,
      ⟨hrep, hnN, ?_⟩, rfl, ?_, ?_⟩
    · funext z
      by_cases hzn : z < n
      · have hs := (hrep.lctCanonRoot_spec (v := z) hzn).2.2.1
        have hzn' : z < (MathForest.empty n).n := hzn
        simp only [rootsOn, hzn, hzn', ↓reduceIte, id]
        exact ForestComp.empty_sameComp hs
      · have hzn' : ¬ z < (MathForest.empty n).n := hzn
        simp [rootsOn, hzn, hzn']
    · obtain ⟨r1, r2, r3, r4, r5⟩ := hresp
      refine ⟨r1, ?_, r3, r4, r5⟩
      show hp' ≤ heap + lctForestAlloc w L N 6 [n, L, P, heap]
      simp only [lctForestAlloc, ↓reduceIte, List.getD_cons_zero, hnN]
      omega
    · show c + lctPhi L st'.mem heap x.n ≤ lctForestRate L n * (n + 1)
      rw [hxn]
      have h1lg : 1 ≤ Nat.log 2 (n + 2) + 1 := by omega
      have hrate : 100000 * (L + 1) ≤ lctForestRate L n := by
        unfold lctForestRate
        calc 100000 * (L + 1) ≤ 1000000 * (L + 1) * 1 := by omega
          _ ≤ 1000000 * (L + 1) * (Nat.log 2 (n + 2) + 1) := Nat.mul_le_mul_left _ h1lg
      exact hc.trans (Nat.mul_le_mul_right _ hrate)
  · intro i b s x args mem pos ω _ hhead hrep hpre hfoot hz hroom
    obtain ⟨F, r⟩ := s
    obtain ⟨hrepL, hnN', hroots⟩ := hrep
    have hnN : F.n ≤ N := hnN'
    obtain ⟨hinv, -, hpre⟩ := hpre
    have hroots' : r = rootsOn F.n (lctCanonRoot mem b F.n) := hroots
    subst hroots'
    have hV : F.Valid := hinv.1
    have hxn : x.n = F.n := hrepL.2.2.2.2.1
    have hphi : lctPhi L mem b F.n ≤ lctPhiBound L N :=
      le_trans hrepL.lctPhi_le_bound (lctPhiBound_mono L hnN)
    have hlg : Nat.log 2 (F.n + 2) + 1 ≤ Nat.log 2 (N + 2) + 1 :=
      Nat.succ_le_succ (Nat.log_mono_right (by omega))
    have hM : 7000 * (L + 1) * (F.n + 2) ≤ 7000 * (L + 1) * (N + 2) := Nat.mul_le_mul_left _ (by omega)
    have hlg1 : 1 ≤ Nat.log 2 (F.n + 2) + 1 := by omega
    rcases i with _ | _ | _ | _ | _ | _ | i
    · obtain ⟨b', v, heap, rfl, hv⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hv' : v < F.n := hv
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := dyn_fit1 (e := 2) hphi (dyn_xl_le (dyn_cF L) hlg) hM (dyn_eS L 2 (by decide)) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hans, -, hcanon, -, hc⟩ :=
        lctFindRootBody_runs (space := lctForestOpSpace L N) p (LctProcs.atBase (b0 + 5)) mem hbase hsp h9 hrepL hv'
          hfoot hz hr1 hs1 ω
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, h1, _, st', c, hrun, (F, rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', hnN, ?_⟩, ⟨rfl, ?_⟩, hresp, ?_⟩
      · funext z; simp only [rootsOn]; split_ifs with hz <;> [exact (hcanon z).symm; rfl]
      · show st'.mem heap = rootsOn F.n (lctCanonRoot mem b F.n) v
        simp only [rootsOn, hv', ↓reduceIte]; exact hans
      · show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
        rw [hx'n, hxn]; unfold lctForestRate; exact dyn_cost0 hc hlg1 (dyn_cF L)
    · obtain ⟨b', a, heap, e, rfl, ha, hedge, heid, hu, hv, hdisc, hfresh, hfitL⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hu' : e.u < F.n := hu; have hv' : e.v < F.n := hv
      have hfe : EdgeFits h L P e := hfitL e (by simp [lctForestModel, MathForest.link])
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := dyn_fit2 (e1 := 7 * L) (e2 := 1) hphi (dyn_xl_le (dyn_cL L) hlg) hM (dyn_eS2 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hcanon⟩ :=
        dynLctLinkWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h2 hrepL hu' hv'
          hdisc hfresh heid hfe hedge ha hfoot hz hr1 hs1
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, hw1, _, st', c, hrun, (F.link e, lctLinkRoots F (rootsOn F.n (lctCanonRoot mem b F.n)) e), x',
        ⟨hrep', hnN, linkRoots_eq hu' hv' hcanon⟩, ⟨e, hedge, rfl⟩, hresp,
        by show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
           rw [hx'n, hxn]; unfold lctForestRate; exact dyn_cost1 hc hlg1 (dyn_cL L) (by clear * -; omega)⟩
    · obtain ⟨b', x1, y1, heap, rfl, -⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := dyn_fit1 (e := 1) hphi (dyn_xl_le (dyn_cC L) hlg) hM (by clear * -; omega) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hcr⟩ :=
        lctCutBody_runs (x := x1) (y := y1) (space := lctForestOpSpace L N) p (LctProcs.atBase (b0 + 5)) mem
          hbase hsp h9 h10 hrepL hfoot hz hr1 hs1 ω
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      have hc' : c + (hpf - heap) + lctPhi L st'.mem b F.n ≤
          lctPhi L mem b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) := hc
      refine ⟨_, h3, _, st', c, hrun, (F.cut x1 y1, lctCutRoots F (rootsOn F.n (lctCanonRoot mem b F.n)) x1 y1), x',
        ⟨hrep', hnN, cutRoots_eq hcr⟩, rfl, hresp,
        by show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
           rw [hx'n, hxn]; unfold lctForestRate; exact dyn_cost0 hc' hlg1 (dyn_cC L)⟩
    · obtain ⟨b', u, v, a, heap, rfl, ha, hva, hsc, hfitA⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := dyn_fit3 (e1 := 18 * L) (e2 := L + 1) (e3 := 200) hphi (dyn_xl_le (dyn_cPA L) hlg) hM
        (dyn_eS3 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hcanon⟩ :=
        dynLctPathAddWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h1 h3 h4
          hrepL hV hsc ha hva (fun e he => hfitA e he) hfoot hz hr1
      have hx'n : x'.n = F.n := by rw [hrep'.2.2.2.2.1, pathAdd_n]
      refine ⟨_, hw2, _, st', c, hrun,
        (F.pathAdd u v (readRat mem a h L P), rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', by show (F.pathAdd u v _).n ≤ N; rw [pathAdd_n]; exact hnN, ?_⟩, rfl,
        respects_mono hresp hs1,
        by show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
           rw [hx'n, hxn]; unfold lctForestRate; exact dyn_cost2 hc hlg1 (dyn_cPA L) (by clear * -; omega)⟩
      · funext z; simp only [rootsOn, pathAdd_n]; split_ifs with hz <;> [exact (hcanon z hz).symm; rfl]
    · obtain ⟨b', u, v, heap, rfl, hsc⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := dyn_fit3 (e1 := 18 * (2 * L + 4)) (e2 := 2 * L + 5) (e3 := 200) hphi
        (dyn_xl_le (dyn_cPM L) hlg) hM (dyn_eS4 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hans, hcanon⟩ :=
        dynLctPathMinWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h1 h3 h5
          hrepL hV hsc hfoot hz hr1
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, hw3, _, st', c, hrun, (F, rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', hnN, ?_⟩, ⟨rfl, hans⟩, respects_mono hresp hs1,
        by show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
           rw [hx'n, hxn]; unfold lctForestRate; exact dyn_cost2 hc hlg1 (dyn_cPM L) (by clear * -; omega)⟩
      · funext z; simp only [rootsOn]; split_ifs with hz <;> [exact (hcanon z hz).symm; rfl]
    · obtain ⟨b', u, v, heap, rfl, hsc, hfits⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := dyn_fit3 (e1 := 18 * L) (e2 := L + 1) (e3 := 200) hphi (dyn_xl_le (dyn_cPS L) hlg) hM
        (dyn_eS3 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hans, hcanon⟩ :=
        dynLctPathSumWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h1 h3 h6
          hrepL hV hsc hfits hfoot hz hr1
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, hw4, _, st', c, hrun, (F, rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', hnN, ?_⟩, ⟨rfl, hans⟩, respects_mono hresp hs1,
        by show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
           rw [hx'n, hxn]; unfold lctForestRate; exact dyn_cost2 hc hlg1 (dyn_cPS L) (by clear * -; omega)⟩
      · funext z; simp only [rootsOn]; split_ifs with hz <;> [exact (hcanon z hz).symm; rfl]
    · exact hpre.elim
end Implements
end MinCostFlow.Final