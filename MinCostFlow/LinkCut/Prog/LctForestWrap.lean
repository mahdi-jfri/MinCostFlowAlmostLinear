module

public import MinCostFlow.LinkCut.Prog.LctModule

/-!
# Queries that keep the roots

The solver's contract asks `pathMin` and `pathSum` to leave the abstract state unchanged, and
`pathAdd` to change only the forest. Our procedures for these operations reroot the tree of `u`
at `u`. So this file wraps them: the wrapper first finds the root `r` of `u` (`findRoot`), runs
the query, copies its answer to the heap pointer of the call, and then reroots the tree back at
`r` with `cut r r` (which changes no edge). If `u = v` it returns at once.

The query answer is written above the cells used by `findRoot`, so the wrapper reserves `A`
words for it at the heap pointer and copies it there at the end. The main result is
`lctWrapTail_runs`, which runs the part after the test `u = v` for any query call `q` that meets
a run statement of the right shape.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section WrapBodies

/-- The part of a wrapper after the test `u = v`. Register `rh` holds the heap pointer and the
query `q` must read the heap pointer from register `21` and leave its own in register `23`. -/
def lctWrapTail (lp : LctProcs) (rh A : ℕ) (q : Stmt) : Stmt :=
  .assign 20 (.bin .add (.reg rh) (.const A)) ;;
  .call 21 lp.findRoot [.reg 0, .reg 1, .reg 20] ;;
  .assign 22 (.load (.reg 20)) ;;
  q ;;
  .call 25 lp.copyWords [.reg 21, .reg rh, .const A] ;;
  .call 24 lp.cut [.reg 0, .reg 22, .reg 22, .reg 23] ;;
  .ret (.reg 24)

/-- A wrapper: if `u = v` return at once, otherwise run `lctWrapTail`. -/
def lctWrapBody (lp : LctProcs) (rh A : ℕ) (q : Stmt) : Stmt :=
  .cond (.bin .eq (.reg 1) (.reg 2)) (.ret (.reg rh)) (lctWrapTail lp rh A q)

theorem lctWrapBody_noRand (lp : LctProcs) (rh A : ℕ) {q : Stmt} (hq : q.NoRand) :
    (lctWrapBody lp rh A q).NoRand := by
  simp [lctWrapBody, lctWrapTail, Stmt.NoRand, hq]

end WrapBodies

section WrapRun

/-- A sum of `log` terms, used to state the budgets below. -/
private theorem wrap_mul3 (a b c k : ℕ) : a * k + b * k + c * k = (a + b + c) * k := by ring

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

/-- The run of `lctWrapTail`. The query `q` runs on the represented forest `F` and leaves the
forest `F1` (with the same vertices and trees); its answer satisfies `Ans` at its heap pointer
and depends only on the `A` words there. At the end the forest is `F1`, the answer is at the heap
pointer `hp` of the call, and every root is as before. -/
theorem lctWrapTail_runs {w h L P b u hp A Cq Eq pos rh : ℕ}
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
    (hr0 : regs 0 = b) (hr1 : regs 1 = u) (hrh : regs rh = hp) (hrh20 : rh < 20)
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
      Runs w p ω (lctWrapTail lp rh A q) { mem := mem₀, regs := regs, pos := pos }
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
  -- Step 1: `r20 := hp + A`.
  let regs1 := Function.update regs 20 (hp + A)
  have hs1 : Runs w p ω (.assign 20 (.bin .add (.reg rh) (.const A)))
      { mem := mem₀, regs := regs, pos := pos } .normal
      { mem := mem₀, regs := regs1, pos := pos } 4 :=
    runs_assign_iff.mpr ⟨hp + A, Expr.eval_add (Expr.eval_reg_of_eq hrh) (Expr.eval_const hA_w)
      hhpA_w, rfl, rfl, rfl⟩
  -- Step 2: `findRoot u` with answer at `hp + A`.
  have hfoot1 : ∀ a, lctFoot b x₀ a → a < hp + A := fun a ha =>
    lt_of_lt_of_le (hfoot a ha) (Nat.le_add_right _ _)
  have hz1 : ZeroFrom mem₀ (hp + A) := hz₀
  rw [← hmul] at hroom
  have hroom_fr : (hp + A) + phi₀ + C_FINDROOT_OP L * logN + 7000 * (L + 1) * (F.n + 2) + 2 <
      2 ^ w := by
    omega
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
  -- Step 3: `r22 := r`.
  let regs3 := Function.update regs2 22 r
  have hs3 : Runs w p ω (.assign 22 (.load (.reg 20)))
      { mem := st_fr.mem, regs := regs2, pos := st_fr.pos } .normal
      { mem := st_fr.mem, regs := regs3, pos := st_fr.pos } 3 := by
    refine runs_assign_iff.mpr ⟨r, Expr.eval_load_of_eq (Expr.eval_reg_of_eq ?_) hans_fr, rfl, rfl,
      rfl⟩
    simp [regs2, regs1]
  -- Step 4: the query.
  have hfoot2 : ∀ a, lctFoot b x1 a → a < hp1 := LctMemRep.foot_lt_of_respects hfoot1 hresp1
  have hz2 : ZeroFrom st_fr.mem hp1 := hresp1.2.2.1
  set phi1 := lctPhi L st_fr.mem b F.n with hphi1
  obtain ⟨hroom_q, hhp1A⟩ := wrap_room_q hroom hc1 hle1
  have hregs3_lo : ∀ i < 20, regs3 i = regs i := fun i hi => by
    simp [regs3, regs2, regs1, Function.update_of_ne (show i ≠ 22 by omega),
      Function.update_of_ne (show i ≠ 21 by omega), Function.update_of_ne (show i ≠ 20 by omega)]
  obtain ⟨hp2, st2, c2, x2, hrun_q, hrep2, hresp2, hc2, hans2, hroots2⟩ :=
    hq st_fr.mem x1 hp1 st_fr.pos regs3 hrep1 hfoot2 hz2 hle1 hroom_q hregs3_lo (by simp [regs3, regs2])
      (fun i hi => hresp1.2.2.2.1 (hp + i) (by omega) (fun hf => by
        have := hfoot _ hf; omega))
  have hle2 : hp1 ≤ hp2 := hresp2.1
  set phi2 := lctPhi L st2.mem b F.n with hphi2
  let regs4 := Function.update regs3 23 hp2
  -- Step 5: copy the answer to `hp`.
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
  have hcall_cp : Runs w p ω (.call 25 lp.copyWords [.reg 21, .reg rh, .const A])
      { mem := st2.mem, regs := regs4, pos := st2.pos } .normal
      { mem := st_cp.mem, regs := regs5, pos := st_cp.pos } (3 + c_cp + 1) := by
    refine runs_call_iff.mpr ⟨[hp1, hp, A], body_cp, o_cp, st_cp, c_cp, ?_, hcp_eq, hrun_cp,
      rfl, by cases st_cp; rfl, rfl⟩
    have h21 : regs4 21 = hp1 := by simp [regs4, regs3, regs2]
    have hrh4 : regs4 rh = hp := by
      simp [regs4, regs3, regs2, regs1, Function.update_of_ne (show rh ≠ 23 by omega),
        Function.update_of_ne (show rh ≠ 22 by omega), Function.update_of_ne (show rh ≠ 21 by omega),
        Function.update_of_ne (show rh ≠ 20 by omega), hrh]
    simp [evalArgs, Expr.eval, h21, hrh4, hA_w]
  -- The footprints stay below or above the answer cells.
  have hfoot_x1 : ∀ a, lctFoot b x1 a → a < hp ∨ hp + A ≤ a := fun a ha => by
    rcases hresp1.2.2.2.2 a ha with h0 | ⟨h1, _⟩
    · exact Or.inl (hfoot a h0)
    · exact Or.inr h1
  have hfoot_x2 : ∀ a, lctFoot b x2 a → a < hp ∨ hp + A ≤ a := fun a ha => by
    rcases hresp2.2.2.2.2 a ha with h0 | ⟨h1, _⟩
    · exact hfoot_x1 a h0
    · exact Or.inr (le_trans hle1 h1)
  have hcp_keep : ∀ a, (a < hp ∨ hp + A ≤ a) → st_cp.mem a = st2.mem a := fun a ha =>
    hcp_out a ha
  have hloc_cp := lctDSRep_local w h L P b F1 x2 st2.mem st_cp.mem
    (fun a ha => (hcp_keep a (hfoot_x2 a ha)).symm)
  have hrep_cp : LctMemRep w h L P b F1 x2 st_cp.mem := hloc_cp.1 hrep2
  have hx2n : x2.n = F.n := by rw [hrep2.2.2.2.2.1, hF1n]
  have hphi_cp : lctPhi L st_cp.mem b F.n = phi2 := by
    have := hloc_cp.2
    simp only [lctDSRep, hx2n] at this
    exact this.symm
  have hfoot_cp : ∀ a, lctFoot b x2 a → a < hp2 := LctMemRep.foot_lt_of_respects hfoot2 hresp2
  have hz_cp : ZeroFrom st_cp.mem hp2 := fun a ha =>
    (hcp_keep a (Or.inr (by omega))).trans (hresp2.2.2.1 a ha)
  -- Step 6: `cut r r` reroots the tree of `u` at `r`.
  have hroom_cut : hp2 + lctPhi L st_cp.mem b F1.n + C_CUT_OP L * (Nat.log 2 (F1.n + 2) + 1) +
      7000 * (L + 1) * (F1.n + 2) + 1 < 2 ^ w := by
    rw [hF1n, hphi_cp]; exact hhp2_w
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
  -- Footprint and memory facts for the whole call.
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
  -- The answer.
  have hans_cp : Ans st_cp.mem hp := hAns _ _ _ _ hans2 (fun i hi => hcp_vals i hi)
  have hans3 : Ans st3.mem hp := by
    refine hAns _ _ _ _ hans_cp (fun i hi => ?_)
    have hnf2 : ¬ lctFoot b x2 (hp + i) := fun h2 => by
      rcases hfoot_x2 _ h2 with h | h <;> omega
    exact hresp3.2.2.2.1 _ (by omega) hnf2
  -- The roots.
  have harena_le : lctArenaHi b (lctCap F.n) ≤ hp := harena_hp
  have hcanon_cp : ∀ z, lctCanonRoot st_cp.mem b F.n z = lctCanonRoot st2.mem b F.n z := by
    intro z
    unfold lctCanonRoot
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
    -- after the query the tree of `u` has root `u`
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
        apply hzu
        have := (hrep₀.lctCanonRoot_spec hz).2.2.1
        rw [h] at this
        exact this
      simp only [hzu, hne, ↓reduceIte]
  -- The budget.
  set phi3 := lctPhi L st3.mem b F.n with hphi3
  refine ⟨hp3, _, _, x3, hrun, hrep3, ⟨by omega, ?_, hresp3.2.2.1, hkeep_lo, hfoot_x3⟩,
    ?_, hans3, hroots⟩
  · rw [← hmul]; exact hhp3_sp
  · rw [← hmul]
    exact hcost

end WrapRun

end MinCostFlow.LinkCut.Prog
