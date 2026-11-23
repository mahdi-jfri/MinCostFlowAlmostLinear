module

public import MinCostFlow.Spanner.ProgTask2InitLoopProof
public import MinCostFlow.Spanner.ProgTask2RoundBase

@[expose] public section

/-!
# Verified Round Phase of `task2Body`

Proves the outer component loop (`t2OuterStep_ptriple`, `t2Round_loop2_ptriple`), bridges Loop 1
(`t2Round_init_loop_ptriple`), Loop 2, and `t2Round_math_spec` into `T2LoopState` for `r_done + 1`
(`t2Round_math_to_loopState`), and concludes `task2Round_triple` for `t2RoundBody`.
-/

namespace MinCostFlow.Spanner

open WordRAM

/-- Outer loop invariant data at component index `ci` during Loop 2 of round `r_done + 1`. -/
structure T2OuterInvData {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (r_done : ℕ)
    (emb₀ : ℕ → Option Walk) (ci : ℕ)
    (g : T2Ghost impl.pathDS) (st : State) (Φ : ℕ) : Prop where
  hr4 : st.regs 4 = inp.v1
  hr10 : st.regs 10 = ctx.wd.comps.length
  hr12 : st.regs 12 = ctx.wd.W.m
  hr20 : st.regs 20 = ci
  hr31 : st.regs 31 = ctx.wInp.prep.aComps
  hr32 : st.regs 32 = st.mem (ctx.wInp.h + 12)
  hr33 : st.regs 33 = ctx.wInp.prep.phiNum_dec
  hr34 : st.regs 34 = ctx.wInp.prep.phiDen_dec
  hr35 : st.regs 35 = ctx.wd.J0_strip.m
  hr36 : st.regs 36 = inp.dsHandlesAddr ctx.wd.W.m
  hr37 : st.regs 37 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length
  hr38 : st.regs 38 = inp.embWJAddr
  hr39 : st.regs 39 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length
  hr40 : st.regs 40 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec
  hr41 : st.regs 41 = r_done + 1
  hr18 : st.regs 18 = g.hCur
  hStep : T2StepInv ctx stc g st.mem
  hVcong : T2VcongRoundInv ctx g
  hη : g.η₁ = r_done + 1
  hemb_prev : g.emb_prev = emb₀
  hq : g.queue = []
  hDr : g.drained = g.procVerts
  hInitC : g.initCountJ = (r_done + 1) * ctx.wd.comps.length
  hInitE : g.initEdgesJ = (r_done + 1) * (ctx.wd.comps.map fun c => c.J_sub.m).sum
  har : stc.nodesEnd ≤ g.arenaPtr
  hcov_prev : ∀ ci' < ci, ∀ eL' < (ctx.wd.comps.getD ci' defaultCompInfo).W_sub.m, t2Covered ctx g ci' eL'
  hZero : ctx.wd.W.m = 0 → g.procVerts = ∅
  hPhi : Φ = t2MidPhi ctx stc g st.mem

/-- Outer loop invariant wrapping `T2OuterInvData` with an existential ghost state. -/
def T2OuterInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (r_done : ℕ)
    (emb₀ : ℕ → Option Walk) (ci : ℕ) (st : State) (Φ : ℕ) : Prop :=
  ∃ g : T2Ghost impl.pathDS, T2OuterInvData ctx stc r_done emb₀ ci g st Φ

private lemma t2_outer_step_cost_arith {c_f rc W_m : ℕ}
    (hrc : rc ≤ W_m * 60 + W_m * 9 + 7)
    (hcf : c_f ≤ rc) :
    6 + (3 + (5 + (5 + (5 + c_f + 1) + 1) + 1) + 1) + 1 ≤ W_m * 69 + 36 := by
  omega

/-- Executes one outer iteration `ci` of Loop 2 (`t2OuterCiBody`). -/
lemma t2OuterStep_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hp_mid : p.procs[selfBase + 3]? = some (t2MiddleEdgeBody dsBase (selfBase + 4)))
    (hp_drain : p.procs[selfBase + 4]? = some (t2DrainQueueBody dsBase))
    {r_done ci : ℕ} {emb₀ : ℕ → Option Walk}
    (hci : ci < ctx.wd.comps.length) :
    PTriple w p
      (T2OuterInv ctx stc r_done emb₀ ci)
      (t2OuterCiBody selfBase)
      (pNormalPost fun st₁ Φ₁ =>
        T2OuterInv ctx stc r_done emb₀ (ci + 1)
          { st₁ with regs := Function.update st₁.regs 20 (ci + 1) } Φ₁ ∧ st₁.regs 20 = ci)
      (fun _ => (ctx.wd.comps.getD ci defaultCompInfo).W_sub.m * 69 + 36) := by
  intro st Φ ω ⟨g, hO⟩
  have db := drain_bounds ctx stc
  have hm := t2_maxWord_scalars ctx stc
  rcases hm with ⟨hv1_ds, _, _, hv1_w, _, _, _, _, _, _⟩
  have hS := hO.hStep
  have hstat := (ctx.agrees_preserves_static hS.agr_pre).2.2.2.2.2.2.2
  rcases t2StaticOut_compExt hstat with ⟨hw20, ha_wAddr, hwNum_eq, hwNum_v1, hCompExt⟩
  set c := ctx.wd.comps[ci]
  set aCompExt := st.mem (ctx.wInp.h + 12)
  set wSubPtr := st.mem (aCompExt + 6 * ci + 1)
  have hce := hCompExt ci hci
  dsimp only at hce
  rcases hce with ⟨hc_wst, hc_2, hc_3, hc_4, hc_wm, hc_G, hc_sub_gt, hc_sub_lt⟩
  have hds_w : stc.dsBaseAddr < 2 ^ w :=
    lt_of_le_of_lt (le_trans db.h_dsc (le_trans db.h_stc db.h_mhe)) db.h_mwb
  have hw_gt1 : 1 < 2 ^ w := ctx.hww.1
  have hsmall_w : ∀ k ≤ 6, k < 2 ^ w := fun k hk => by omega
  have hci_w : ci < 2 ^ w := by
    have : ci < ctx.wd.comps.length := hci
    have : ctx.wd.comps.length ≤ inp.v1 := by omega
    omega
  have h6ci_w : 6 * ci < 2 ^ w := by omega
  have ha6_w : aCompExt + 6 * ci < 2 ^ w := by omega
  have ha6_1_w : aCompExt + 6 * ci + 1 < 2 ^ w := by omega
  have ha6_5_w : aCompExt + 6 * ci + 5 < 2 ^ w := by omega
  have hc_wm_w : c.W_sub.m < 2 ^ w := by dsimp only [c]; omega
  have hvho_ci_w : inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci < 2 ^ w := by
    have := db.e_vho; have := db.e_del; have := db.e_vh; have := db.e_vhd
    have := db.e_vc; have := db.e_ps; have := db.e_ew; have := db.e_q
    have := db.h_nlo; have := db.h_nds; omega
  let s21 : State := { st with regs := Function.update st.regs 21 (aCompExt + 6 * ci) }
  have hr21 : Runs w p ω (Stmt.assign 21 (t2Add (.reg 32) (t2Mul (.const 6) (.reg 20))))
      st .normal s21 6 := by
    have he := Expr.eval_add (Expr.eval_reg_of_eq hO.hr32)
      (Expr.eval_mul (Expr.eval_const (hsmall_w 6 (by decide))) (Expr.eval_reg_of_eq hO.hr20) h6ci_w) ha6_w
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
  let s22 : State := { s21 with regs := Function.update s21.regs 22 c.wStart }
  have hr22 : Runs w p ω (Stmt.assign 22 (.load (.reg 21))) s21 .normal s22 3 := by
    have h21 : s21.regs 21 = aCompExt + 6 * ci := by dsimp only [s21]; exact Function.update_self _ _ _
    have he := Expr.eval_load (w := w) (Expr.eval_reg_of_eq h21)
    change Expr.eval w s21 (.load (.reg 21)) = some (st.mem (aCompExt + 6 * ci)) at he
    rw [hc_wst] at he
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
  let s23 : State := { s22 with regs := Function.update s22.regs 23 wSubPtr }
  have hr23 : Runs w p ω (Stmt.assign 23 (t2Ld (.reg 21) (.const 1))) s22 .normal s23 5 := by
    have h21 : s22.regs 21 = aCompExt + 6 * ci := by
      simp (disch := decide) only [s22, s21, Function.update_of_ne, Function.update_self]
    have he := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h21)
      (Expr.eval_const (hsmall_w 1 (by decide))) ha6_1_w)
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
  let s24 : State := { s23 with regs := Function.update s23.regs 24 c.W_sub.m }
  have hr24 : Runs w p ω (Stmt.assign 24 (t2Ld (.reg 21) (.const 5))) s23 .normal s24 5 := by
    have h21 : s23.regs 21 = aCompExt + 6 * ci := by
      simp (disch := decide) only [s23, s22, s21, Function.update_of_ne, Function.update_self]
    have he := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h21)
      (Expr.eval_const (hsmall_w 5 (by decide))) ha6_5_w)
    change Expr.eval w s23 (t2Ld (.reg 21) (.const 5)) = some (st.mem (aCompExt + 6 * ci + 5)) at he
    rw [hc_wm] at he
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
  let s25 : State := { s24 with regs := Function.update s24.regs 25 (vhatBase ctx.wd ci) }
  have hr25 : Runs w p ω (Stmt.assign 25 (t2Ld (.reg 37) (.reg 20))) s24 .normal s25 5 := by
    have h37 : s24.regs 37 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length := by
      simp (disch := decide) only [s24, s23, s22, s21, Function.update_of_ne, hO.hr37]
    have h20 : s24.regs 20 = ci := by
      simp (disch := decide) only [s24, s23, s22, s21, Function.update_of_ne, hO.hr20]
    have he := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h37) (Expr.eval_reg_of_eq h20) hvho_ci_w)
    change Expr.eval w s24 (t2Ld (.reg 37) (.reg 20)) =
      some (st.mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci)) at he
    rw [hS.hVho ci hci] at he
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
  have hfor := PTriple.forRange_le (w := w) (p := p)
    (P := fun st_f Φ_f => st_f = s25 ∧ Φ_f = Φ)
    (r := 27) (lo := .const 0) (hi := .reg 24) (body := t2InnerCiBody selfBase)
    (Inv := T2InnerInv ctx stc r_done emb₀ ci wSubPtr)
    (stepCost := fun _ => 60)
    0 c.W_sub.m (Nat.zero_le _) hw_gt1 (fun _ => hc_wm_w)
    (fun st_f Φ_f ⟨hstf, hΦf⟩ => by
      subst hstf hΦf
      refine ⟨Expr.eval_const (by omega : 0 < 2 ^ w), ?_⟩
      refine ⟨g,
        { hr4 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr4]
          hr10 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr10]
          hr12 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr12]
          hr20 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr20]
          hr22 := by
            dsimp only
            rw [Function.update_of_ne (by decide : (22 : ℕ) ≠ 27)]
            have h22 : s25.regs 22 = c.wStart := by
              simp (disch := decide) only [s25, s24, s23, s22, Function.update_of_ne, Function.update_self]
            rw [h22, List.getElem?_eq_getElem hci]; rfl
          hr23 := by
            simp (disch := decide) only [s25, s24, s23, Function.update_of_ne, Function.update_self]
          hr24 := by
            dsimp only
            rw [Function.update_of_ne (by decide : (24 : ℕ) ≠ 27)]
            have h24 : s25.regs 24 = c.W_sub.m := by
              simp (disch := decide) only [s25, s24, Function.update_of_ne, Function.update_self]
            rw [h24, List.getElem?_eq_getElem hci]; rfl
          hr25 := by
            dsimp only
            rw [Function.update_of_ne (by decide : (25 : ℕ) ≠ 27)]
            dsimp only [s25]
            exact Function.update_self _ _ _
          hr27 := by dsimp only; exact Function.update_self _ _ _
          hr31 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr31]
          hr32 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr32]
          hr33 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr33]
          hr34 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr34]
          hr35 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr35]
          hr36 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr36]
          hr37 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr37]
          hr38 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr38]
          hr39 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr39]
          hr40 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr40]
          hr41 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr41]
          hwSub_g := fun _ => ⟨rfl, hc_G, hc_sub_lt⟩
          hr18 := by simp (disch := decide) only [s25, s24, s23, s22, s21, Function.update_of_ne, hO.hr18]
          hStep := hO.hStep
          hVcong := hO.hVcong
          hη := hO.hη
          hemb_prev := hO.hemb_prev
          hq := hO.hq
          hDr := hO.hDr
          hInitC := hO.hInitC
          hInitE := hO.hInitE
          har := hO.har
          hcov_prev := hO.hcov_prev
          hcov_cur := fun _ h => absurd h (Nat.not_lt_zero _)
          hPhi := hO.hPhi }⟩)
    (fun _ _ _ _ _ ⟨_, hi⟩ => hi.hr27)
    (fun _ st_i _ _ _ ⟨_, hi⟩ => by
      have h24 : st_i.regs 24 = c.W_sub.m := by rw [hi.hr24, List.getElem?_eq_getElem hci]; rfl
      exact Expr.eval_reg_of_eq h24)
    (fun eL _ heL => t2InnerStep_ptriple ctx stc hSpec hp_mid hp_drain hci heL)
  obtain ⟨o_f, st_f, c_f, Φ_f, hr_f, hq_f, hc_f⟩ := hfor s25 Φ ω ⟨rfl, rfl⟩
  cases o_f with
  | returned _ => exact absurd hq_f (by simp)
  | normal =>
    rcases hq_f with ⟨g_f, hI_f⟩
    have hrun := runs_seq_iff.mpr (Or.inr ⟨s21, 6, _, hr21,
      runs_seq_iff.mpr (Or.inr ⟨s22, 3, _, hr22,
        runs_seq_iff.mpr (Or.inr ⟨s23, 5, _, hr23,
          runs_seq_iff.mpr (Or.inr ⟨s24, 5, _, hr24,
            runs_seq_iff.mpr (Or.inr ⟨s25, 5, c_f, hr25, hr_f, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hcov_next : ∀ ci' < ci + 1,
        ∀ eL' < (ctx.wd.comps.getD ci' defaultCompInfo).W_sub.m, t2Covered ctx g_f ci' eL' := by
      intro ci' hci' eL' heL'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hci' with hlt | heq
      · exact hI_f.hcov_prev ci' hlt eL' heL'
      · rw [heq] at heL' ⊢
        rw [List.getD_eq_getElem _ _ hci] at heL'
        exact hI_f.hcov_cur eL' heL'
    have hZero_next : ctx.wd.W.m = 0 → g_f.procVerts = ∅ := fun hm0 => by
      have hm_ge := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hw_sum : (ctx.wd.comps.map fun c => c.W_sub.m).sum ≥ c.W_sub.m := by
        have hmem : c.W_sub.m ∈ ctx.wd.comps.map fun x => x.W_sub.m :=
          List.mem_map_of_mem (List.getElem_mem hci)
        exact List.le_sum_of_mem hmem
      have hw_eq := ctx.hw_okW.W_m_eq
      dsimp only [c] at hw_sum
      omega
    let stOut := { st_f with regs := Function.update st_f.regs 20 (ci + 1) }
    have hO_next : T2OuterInvData ctx stc r_done emb₀ (ci + 1) g_f stOut Φ_f :=
      { hr4 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr4]
        hr10 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr10]
        hr12 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr12]
        hr20 := by dsimp only [stOut]; exact Function.update_self _ _ _
        hr31 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr31]
        hr32 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr32]
        hr33 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr33]
        hr34 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr34]
        hr35 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr35]
        hr36 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr36]
        hr37 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr37]
        hr38 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr38]
        hr39 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr39]
        hr40 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr40]
        hr41 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr41]
        hr18 := by simp (disch := decide) only [stOut, Function.update_of_ne, hI_f.hr18]
        hStep := hI_f.hStep
        hVcong := hI_f.hVcong
        hη := hI_f.hη
        hemb_prev := hI_f.hemb_prev
        hq := hI_f.hq
        hDr := hI_f.hDr
        hInitC := hI_f.hInitC
        hInitE := hI_f.hInitE
        har := hI_f.har
        hcov_prev := hcov_next
        hZero := hZero_next
        hPhi := hI_f.hPhi }
    have hcost_f : c_f + Φ_f ≤ (c.W_sub.m * 60 + c.W_sub.m * 9 + 7) + Φ := by
      have hrc : rangeCost (fun _ : ℕ => 60) 0 c.W_sub.m = c.W_sub.m * 60 := by
        rw [rangeCost_zero_eq_sum]
        simp [Finset.sum_const, smul_eq_mul]
      have hsz1 : (Expr.const 0).size = 1 := rfl
      have hsz2 : (Expr.reg 24).size = 1 := rfl
      rw [hrc, hsz1, hsz2, Nat.sub_zero] at hc_f
      exact hc_f
    have hrc_tr : (6 + (3 + (5 + (5 + (5 + c_f + 1) + 1) + 1) + 1) + 1) + Φ_f ≤
        ((ctx.wd.comps.getD ci defaultCompInfo).W_sub.m * 69 + 36) + Φ := by
      rw [List.getD_eq_getElem _ _ hci]
      dsimp only [c] at hcost_f ⊢
      omega
    exact ⟨.normal, st_f, _, Φ_f, hrun, ⟨⟨g_f, hO_next⟩, hI_f.hr20⟩, hrc_tr⟩

private lemma t2_sum_wsub_le {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    ∑ ci ∈ Finset.range ctx.wd.comps.length,
        ((ctx.wd.comps.getD ci defaultCompInfo).W_sub.m * 69 + 36) ≤
      69 * ctx.wd.W.m + 36 * ctx.wd.comps.length := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm _ 36]
  have hsum : (∑ ci ∈ Finset.range ctx.wd.comps.length,
      (ctx.wd.comps.getD ci defaultCompInfo).W_sub.m * 69) =
      (∑ ci ∈ Finset.range ctx.wd.comps.length,
        (ctx.wd.comps.getD ci defaultCompInfo).W_sub.m) * 69 := by
    rw [Finset.sum_mul]
  rw [hsum, sum_range_getD_nat ctx.wd.comps defaultCompInfo (fun c => c.W_sub.m)]
  have hw_eq := ctx.hw_okW.W_m_eq
  nlinarith

private lemma t2_loop2_cost_arith {W_m K mw m c_l2 Φ_2 rc_l2 Φ_1 : ℕ}
    (hWm : W_m ≤ mw) (hKm : K ≤ m)
    (hrc : rc_l2 ≤ 69 * W_m + 36 * K)
    (hcl2 : c_l2 + Φ_2 ≤ rc_l2 + K * 9 + 7 + Φ_1) :
    c_l2 + Φ_2 ≤ 45 * m + 69 * mw + 7 + Φ_1 := by
  nlinarith

/-- Runs Loop 2 (`forRange 20 (.const 0) (.reg 10) (t2OuterCiBody selfBase)`) across all components. -/
lemma t2Round_loop2_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hp_mid : p.procs[selfBase + 3]? = some (t2MiddleEdgeBody dsBase (selfBase + 4)))
    (hp_drain : p.procs[selfBase + 4]? = some (t2DrainQueueBody dsBase))
    {r_done : ℕ} {emb₀ : ℕ → Option Walk} :
    PTriple w p
      (fun st Φ => ∃ g : T2Ghost impl.pathDS,
        T2OuterInvData ctx stc r_done emb₀ 0 g
          { mem := st.mem, regs := Function.update st.regs 20 0, pos := st.pos } Φ)
      (forRange 20 (.const 0) (.reg 10) (t2OuterCiBody selfBase))
      (pNormalPost (T2OuterInv ctx stc r_done emb₀ ctx.wd.comps.length))
      (fun _ => 45 * inp.J.m + 69 * Task1Input.mwCap impl inp.J + 7) := by
  intro st Φ ω ⟨g₀, hO₀⟩
  have hK_w : 0 < ctx.wd.comps.length → ctx.wd.comps.length < 2 ^ w := fun _ => by
    have hK_le : ctx.wd.comps.length ≤ inp.J.m := ctx.hK_le
    have h1 : 1 ≤ Task2Input.eta1Cap impl inp.J := by
      unfold Task2Input.eta1Cap; exact Nat.le_add_right 1 _
    have hm_eta := (t2_maxWord_scalars ctx stc).2.2.2.2.2.2.2.1
    exact lt_of_le_of_lt (le_trans hK_le (by simpa using Nat.mul_le_mul h1 le_rfl)) hm_eta
  have hfor := PTriple.forRange_le (w := w) (p := p)
    (P := fun st Φ => ∃ g : T2Ghost impl.pathDS,
      T2OuterInvData ctx stc r_done emb₀ 0 g
        { mem := st.mem, regs := Function.update st.regs 20 0, pos := st.pos } Φ)
    (r := 20) (lo := .const 0) (hi := .reg 10) (body := t2OuterCiBody selfBase)
    (Inv := T2OuterInv ctx stc r_done emb₀)
    (stepCost := fun ci => (ctx.wd.comps.getD ci defaultCompInfo).W_sub.m * 69 + 36)
    0 ctx.wd.comps.length (Nat.zero_le _) ctx.hww.1 hK_w
    (fun st_f Φ_f ⟨g_f, hO_f⟩ =>
      ⟨Expr.eval_const (by have := ctx.hww.1; omega : 0 < 2 ^ w), ⟨g_f, hO_f⟩⟩)
    (fun _ _ _ _ _ ⟨_, hi⟩ => hi.hr20)
    (fun _ _ _ _ _ ⟨_, hi⟩ => Expr.eval_reg_of_eq hi.hr10)
    (fun ci _ hci => t2OuterStep_ptriple ctx stc hSpec hp_mid hp_drain hci)
  obtain ⟨o_f, st_f, c_f, Φ_f, hr_f, hq_f, hc_f⟩ := hfor st Φ ω ⟨g₀, hO₀⟩
  have hrc_eq : rangeCost (fun ci => (ctx.wd.comps.getD ci defaultCompInfo).W_sub.m * 69 + 36)
      0 ctx.wd.comps.length =
      ∑ ci ∈ Finset.range ctx.wd.comps.length,
        ((ctx.wd.comps.getD ci defaultCompInfo).W_sub.m * 69 + 36) :=
    rangeCost_zero_eq_sum _ _
  have hsz1 : (Expr.const 0).size = 1 := rfl
  have hsz2 : (Expr.reg 10).size = 1 := rfl
  rw [hrc_eq, hsz1, hsz2, Nat.sub_zero] at hc_f
  exact ⟨o_f, st_f, c_f, Φ_f, hr_f, hq_f,
    t2_loop2_cost_arith ctx.hmW_le ctx.hK_le (t2_sum_wsub_le ctx) hc_f⟩

private lemma t2_round_reassoc {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {a1 a2 a3 a4 f1 t : Stmt} {st sm sf : State} {o : Outcome} {c1 c2 : ℕ}
    (h1 : Runs w p ω (a1 ;; a2 ;; a3 ;; a4 ;; f1) st .normal sm c1)
    (h2 : Runs w p ω t sm o sf c2) :
    Runs w p ω (a1 ;; a2 ;; a3 ;; a4 ;; f1 ;; t) st o sf (c1 + c2 + 1) := by
  rcases runs_seq_iff.mp h1 with ⟨_, _, _, hne, _⟩ | ⟨s1, ca1, r1, ha1, hr1, rfl⟩
  · cases hne
  rcases runs_seq_iff.mp hr1 with ⟨_, _, _, hne, _⟩ | ⟨s2, ca2, r2, ha2, hr2, rfl⟩
  · cases hne
  rcases runs_seq_iff.mp hr2 with ⟨_, _, _, hne, _⟩ | ⟨s3, ca3, r3, ha3, hr3, rfl⟩
  · cases hne
  rcases runs_seq_iff.mp hr3 with ⟨_, _, _, hne, _⟩ | ⟨s4, ca4, cf1, ha4, hf1, rfl⟩
  · cases hne
  have h5 := runs_seq_iff.mpr (Or.inr ⟨sm, cf1, c2, hf1, h2, rfl⟩)
  have h4 := runs_seq_iff.mpr (Or.inr ⟨s4, ca4, cf1 + c2 + 1, ha4, h5, rfl⟩)
  have h3 := runs_seq_iff.mpr (Or.inr ⟨s3, ca3, _, ha3, h4, rfl⟩)
  have h2' := runs_seq_iff.mpr (Or.inr ⟨s2, ca2, _, ha2, h3, rfl⟩)
  exact runs_seq_iff.mpr (Or.inr ⟨s1, ca1, _, ha1, h2', by omega⟩)

private lemma composeAux_congr {B B' : Cited.Graph} {f f' : ℕ → Walk}
    {vs es : List ℕ} (hB : B = B') (hf : ∀ e ∈ es, f e = f' e) :
    composeAux B f vs es = composeAux B' f' vs es := by
  subst hB
  induction vs generalizing es with
  | nil =>
    rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
    rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
  | cons u rest ih =>
    cases rest with
    | nil =>
      rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
      rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
    | cons v vs' =>
      cases es with
      | nil =>
        rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ _ h => by cases h)]
        rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ _ h => by cases h)]
      | cons j js =>
        rw [composeAux.eq_1, composeAux.eq_1, hf j List.mem_cons_self,
          ih (fun e he => hf e (List.mem_cons_of_mem j he))]

private lemma partialToWalk_edges_lt {W J : Cited.Graph} {emb : ℕ → Option Walk}
    (hP : IsPartialEmbedding W J emb) {eW : ℕ} (heW : eW < W.m) :
    ∀ e ∈ (partialToWalk emb eW).edges, e < J.m := by
  intro e he
  dsimp only [partialToWalk] at he
  cases h : emb eW with
  | none => simp [h, Walk.empty] at he
  | some P =>
    simp only [h] at he
    rcases hP.2 eW heW P h with ⟨_, _, ⟨_, hpe, _⟩ | ⟨_, _, _, _, hedges, _⟩⟩
    · simp [hpe] at he
    · exact hedges e he

private lemma vcongAt_compose_partial_congr {W J J' : Cited.Graph} {wW : ℕ → ℝ}
    {f f' : ℕ → Walk} {emb : ℕ → Option Walk}
    (hJ : J' = J) (hPart : IsPartialEmbedding W J emb)
    (hf : ∀ e < J.m, f e = f' e) (x : ℕ) :
    vcongAt W wW (compose J' f' (partialToWalk emb)) x =
      vcongAt W wW (compose J f (partialToWalk emb)) x := by
  have hcomp : ∀ eW < W.m,
      compose J' f' (partialToWalk emb) eW = compose J f (partialToWalk emb) eW := fun eW heW =>
    composeAux_congr hJ fun e he => (hf e (partialToWalk_edges_lt hPart heW e he)).symm
  unfold vcongAt
  have hflt : (Finset.range W.m).filter (fun j => x ∈ (compose J' f' (partialToWalk emb) j).verts) =
      (Finset.range W.m).filter (fun j => x ∈ (compose J f (partialToWalk emb) j).verts) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨hj, hx⟩ => ⟨hj, hcomp j hj ▸ hx⟩, fun ⟨hj, hx⟩ => ⟨hj, (hcomp j hj).symm ▸ hx⟩⟩
  rw [hflt]

/-- Converts the completed round invariant (`T2OuterInvData` at `ci = K`) and post-`reg 19` state
into `T2LoopState` for `r_done + 1` via `t2Round_math_spec`. -/
lemma t2Round_math_to_loopState {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) {r_done : ℕ}
    {emb₀ : ℕ → Option Walk} {g : T2Ghost impl.pathDS} {st₂ st_fin : State} {Φ₂ : ℕ}
    (hO : T2OuterInvData ctx stc r_done emb₀ ctx.wd.comps.length g st₂ Φ₂)
    (hMem : st_fin.mem = st₂.mem)
    (hReg : ∀ r ≠ 19, st_fin.regs r = st₂.regs r)
    (hr19 : st_fin.regs 19 = (unembeddedSetPure ctx.wd g.emb).card) :
    T2LoopState ctx stc (r_done + 1) emb₀ g.emb g.hCur g.arenaPtr g.deleteCountJ
      g.vcongUpdates g.innerIters1 st_fin := by
  have hS := hO.hStep
  have hStat := (ctx.agrees_preserves_static hS.agr_pre).2.2.2.2.2.2.1
  have hZeroAll : ctx.wd.W.m = 0 →
      g.procVerts = ∅ ∧ ∀ ci < ctx.wd.comps.length, (g.states ci).deleted = ∅ := fun hm0 => by
    have hp := hO.hZero hm0
    refine ⟨hp, fun ci hci => ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨_, x, hx, _⟩ := hS.hDelSub ci hci b hb
    simp [hp] at hx
  have hVhatSub : ∀ ci (hci : ci < ctx.wd.comps.length),
      (g.states ci).Vhat ⊆ ctx.wd.comps[ci].J_sub.verts := fun ci hci => by
    rcases (hS.hDS.at_ci ci hci).2.2.2.2 with
      ⟨hG, _, _, _, _, _, _, _, _, _, _, hVh_sub, _, _⟩
    have hG' : (g.states ci).G = ctx.wd.comps[ci].J_sub := by
      simpa only [List.getD_eq_getElem _ _ hci] using hG
    rw [← hG']
    exact hVh_sub
  have hVhatVol : ∀ ci (hci : ci < ctx.wd.comps.length),
      (ctx.wd.comps[ci].J_sub.vol (g.states ci).Vhat : ℝ) ≤
        ctx.wd.γ_del * ((g.states ci).deleted.card : ℝ) / ctx.wd.φ_ds := fun ci hci => by
    rcases (hS.hDS.at_ci ci hci).2.2.2.2 with
      ⟨hG, hpn, hpd, hM, _, _, _, _, _, _, _, _, _, hvol⟩
    have hG' : (g.states ci).G = ctx.wd.comps[ci].J_sub := by
      simpa only [List.getD_eq_getElem _ _ hci] using hG
    have hφ_eq : (g.states ci).φ_in = ctx.wd.φ_dec := by
      simp [PathDSAbsState.φ_in, WitnessCoreInput.mkWitnessData, hpn, hpd]
    rw [← hG']
    have h1 := hvol
    rw [hφ_eq, hM] at h1
    have hds := ctx.ds_bounds
    have hγ_le : impl.pathDS.params.γ_del ctx.wd.φ_dec ctx.wd.J0_strip.m ≤ ctx.wd.γ_del := hds.2.2.2.2.2.2.1
    have hφ_le : ctx.wd.φ_ds ≤ impl.pathDS.params.φ_out ctx.wd.φ_dec ctx.wd.J0_strip.m := hds.2.2.2.2.2.2.2.1
    have hmul : impl.pathDS.params.γ_del ctx.wd.φ_dec ctx.wd.J0_strip.m * ((g.states ci).deleted.card : ℝ) ≤
        ctx.wd.γ_del * ((g.states ci).deleted.card : ℝ) :=
      mul_le_mul_of_nonneg_right hγ_le (Nat.cast_nonneg _)
    have hdiv : impl.pathDS.params.γ_del ctx.wd.φ_dec ctx.wd.J0_strip.m * ((g.states ci).deleted.card : ℝ) /
          impl.pathDS.params.φ_out ctx.wd.φ_dec ctx.wd.J0_strip.m ≤
        ctx.wd.γ_del * ((g.states ci).deleted.card : ℝ) / ctx.wd.φ_ds :=
      div_le_div₀ (mul_nonneg (by linarith [ctx.hw_okW.γ_del_ge]) (Nat.cast_nonneg _))
        hmul ctx.hw_okW.φ_ds_pos hφ_le
    exact le_trans h1 hdiv
  have hCov : ∀ ci (hci : ci < ctx.wd.comps.length),
      ∀ eL < ctx.wd.comps[ci].W_sub.m,
        g.emb (ctx.wd.comps[ci].wStart + eL) = none →
          (ctx.wd.comps[ci].W_sub.edges.getD eL (0, 0)).1 ∈ (g.states ci).Vhat ∨
            (ctx.wd.comps[ci].W_sub.edges.getD eL (0, 0)).2 ∈ (g.states ci).Vhat := by
    intro ci hci eL heL hnone
    have heL' : eL < (ctx.wd.comps.getD ci defaultCompInfo).W_sub.m := by
      simpa only [List.getD_eq_getElem _ _ hci] using heL
    have htc := hO.hcov_prev ci hci eL heL'
    simp only [t2Covered, List.getD_eq_getElem _ _ hci] at htc
    rcases htc with h1 | h2 | h3
    · rw [hnone] at h1; simp at h1
    · exact Or.inl h2
    · exact Or.inr h3
  have hMono' : ∀ eW < ctx.wd.W.m, emb₀ eW = none ∨ g.emb eW = emb₀ eW := by
    have := hS.hMono
    rwa [hO.hemb_prev] at this
  have hPart_emb0 : IsPartialEmbedding ctx.wd.W inp.J emb₀ := by
    refine ⟨hS.hPart.1, fun eW heW P hP => ?_⟩
    rcases hMono' eW heW with hnone | heq
    · rw [hP] at hnone; cases hnone
    · exact hS.hPart.2 eW heW P (heq.trans hP)
  have hPart' : IsPartialEmbedding ctx.wd.W ctx.wInp.prep.J g.emb := by
    rw [ctx.hWInpJ]; exact hS.hPart
  have hembJH' : IsEmbedding ctx.wInp.prep.J ctx.wInp.H' ctx.wInp.embJH := by
    rw [ctx.hWInpJ, ctx.hWInpH']
    refine ⟨ctx.hembJH.1, fun j hj => ?_⟩
    rw [ctx.hWInpEmb j hj]
    exact ctx.hembJH.2 j hj
  have hVc_prev' : ∀ x < ctx.wInp.H'.n,
      vcongAt ctx.wd.W ctx.wd.wW (compose ctx.wInp.prep.J ctx.wInp.embJH (partialToWalk emb₀)) x ≤
        ((r_done : ℝ) + 1 / 2) * ctx.wd.τ₁ := fun x hx => by
    rw [ctx.hWInpH'] at hx
    rw [vcongAt_compose_partial_congr ctx.hWInpJ hPart_emb0 (fun e he => (ctx.hWInpEmb e he).symm) x]
    have := hS.hVc_prev x hx
    rwa [hO.hη, Nat.add_sub_cancel, hO.hemb_prev] at this
  have hProcSub' : ∀ x ∈ g.procVerts,
      x < ctx.wInp.H'.n ∧
        ((r_done + 1 : ℕ) : ℝ) * ctx.wd.τ₁ ≤
          vcongAt ctx.wd.W ctx.wd.wW (compose ctx.wInp.prep.J ctx.wInp.embJH (partialToWalk g.emb)) x := by
    intro x hx
    have h1 := hS.hProcSub x hx
    rw [hO.hη] at h1
    refine ⟨ctx.hWInpH'.symm ▸ h1.1, ?_⟩
    rw [vcongAt_compose_partial_congr ctx.hWInpJ hS.hPart (fun e he => (ctx.hWInpEmb e he).symm) x]
    exact h1.2
  have hDelSub' : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length),
      ∀ b ∈ (g.states ci).deleted, b < ctx.wd.comps[ci].J_sub.m ∧
        ∃ x ∈ g.procVerts, x ∈ (ctx.wInp.embJH (ctx.wd.comps[ci].jSubOrigEdges.getD b 0)).verts := by
    intro ci hci b hb
    obtain ⟨hb_lt, x, hx, hxv⟩ := hS.hDelSub ci hci b hb
    rcases (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 with
      ⟨hlen, _, hj_lt, _⟩
    have hlt_j : ctx.wd.comps[ci].jSubOrigEdges.getD b 0 < inp.J.m := by
      have hmem : ctx.wd.comps[ci].jSubOrigEdges.getD b 0 ∈ ctx.wd.comps[ci].jSubOrigEdges := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      rw [← ctx.hWInpJ]; exact hj_lt _ hmem
    refine ⟨hb_lt, x, hx, ?_⟩
    rw [ctx.hWInpEmb _ hlt_j]
    exact hxv
  have hmath := t2Round_math_spec hStat ctx.hw_okW ctx.hws hembJH'
    hMono' hPart' hS.hj0 hS.hELen hVc_prev' hProcSub'
    hVhatSub hVhatVol hDelSub' hCov hZeroAll
  have hGet_eq : g.getPathCountJ =
      ctx.wd.W.m - ctx.wd.j0Edges.length - (unembeddedSetPure ctx.wd g.emb).card :=
    Nat.eq_sub_of_add_eq hS.hGetC
  have hVol_cur' : volWRemPure ctx.wd g.emb ≤
      (2 * ctx.wd.c_deg / (2 * ctx.wd.c_deg + 1)) ^ (r_done + 1) * (ctx.wd.c_deg * (inp.J.m : ℝ)) := by
    have hprev := hS.hVol_prev
    rw [hO.hη, Nat.add_sub_cancel, hO.hemb_prev] at hprev
    have hcdeg := ctx.hw_okW.c_deg_ge
    have hr_nn : (0 : ℝ) ≤ 2 * ctx.wd.c_deg / (2 * ctx.wd.c_deg + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hprev hr_nn
    rw [← mul_assoc, ← pow_succ'] at hmul
    exact le_trans hmath.2.1 hmul
  have hDel_le' : g.deleteCountJ ≤ (r_done + 1) * inp.J.m := by
    have hp := hS.hPrevDel
    rw [hO.hη, Nat.add_sub_cancel] at hp
    have hd := hS.hDelEq
    have hs := hmath.2.2.1
    rw [ctx.hWInpJ] at hs
    change ∑ ci ∈ Finset.range ctx.wd.comps.length, (g.states ci).deleted.card ≤ inp.J.m at hs
    rw [Nat.add_mul, Nat.one_mul]
    omega
  refine
    { hr4 := (hReg 4 (by decide)).trans hO.hr4
      hr10 := (hReg 10 (by decide)).trans hO.hr10
      hr12 := (hReg 12 (by decide)).trans hO.hr12
      hr18 := (hReg 18 (by decide)).trans hO.hr18
      hr19 := by simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, hr19]
      hr31 := (hReg 31 (by decide)).trans hO.hr31
      hr32 := by rw [hMem]; exact (hReg 32 (by decide)).trans hO.hr32
      hr33 := (hReg 33 (by decide)).trans hO.hr33
      hr34 := (hReg 34 (by decide)).trans hO.hr34
      hr35 := (hReg 35 (by decide)).trans hO.hr35
      hr36 := (hReg 36 (by decide)).trans hO.hr36
      hr37 := (hReg 37 (by decide)).trans hO.hr37
      hr38 := (hReg 38 (by decide)).trans hO.hr38
      hr39 := (hReg 39 (by decide)).trans hO.hr39
      hr40 := (hReg 40 (by decide)).trans hO.hr40
      agr_pre := by rw [hMem]; exact hS.agr_pre
      h_v1_slots := by
        rw [hMem]
        refine ⟨hS.h0, hO.hη ▸ hS.h1, hO.hInitC ▸ hS.h2, hO.hInitE ▸ hS.h3, hGet_eq ▸ hS.h4,
          hS.h5, hS.h6, hS.h7, hS.h8, hS.h9, hS.h10, hS.h12, hS.h13, hS.h14, hS.h15, hS.h16,
          hS.h17, hS.h18, hS.h19, hS.h20, hS.h21, hS.h22, hS.h23, hS.h24, hS.h25,
          by rw [hS.h26, hS.hQid, hGet_eq], by rw [hS.h27, hO.hq, List.length_nil],
          by rw [hS.h28, hO.hη], hS.h29, hS.h30, hS.h31⟩
      hCeb := by rw [hMem]; exact hS.hCeb
      hVho := by rw [hMem]; exact hS.hVho
      hDelR_le := fun ci hci b hb => by rw [hMem, ← hO.hη]; exact (hS.hDelR ci hci b hb).1
      hVhatS_le := fun ci hci y hy => by rw [hMem, ← hO.hη]; exact (hS.hVhatS ci hci y hy).1
      hProcS_le := fun x hx => by rw [hMem, ← hO.hη]; exact (hS.hProcS x hx).1
      hInc := by rw [hMem]; exact hS.hInc
      hVc := by rw [hMem]; exact hS.hVc
      hEwSt := fun x hx => by
        rw [hMem, ← hGet_eq, ← hS.hQid]; exact hS.hEwSt x hx
      hEmb := by rw [hMem]; exact hS.hEmb
      hAr_lo := hO.har
      hAr_le := by rw [← hGet_eq]; exact hS.hAr_le
      hGet_le := by have := hS.hGetC; omega
      hPart := hS.hPart
      hj0 := hS.hj0
      hELen := hS.hELen
      hVc_cur := by simpa only [hO.hη] using hO.hVcong.1
      hVol_cur := hVol_cur'
      hPrev_bd := fun h => absurd h (Nat.succ_ne_zero _)
      hDel_le := hDel_le'
      hVcU_le := by rw [← hGet_eq]; exact hS.hVcUpd
      hInn_le := by
        rw [← hGet_eq]
        have hi := hS.hInner
        rw [hO.hq, List.length_nil, Nat.cast_zero, add_zero] at hi
        exact hi
      hCur_lo := hS.hDS.h_ge
      hCur_le := by rw [← hO.hInitC, ← hGet_eq]; exact hS.hHCur_le
      hzf := by rw [hMem]; exact hS.hDS.zero_from }

private lemma t2Round_total_cost_arith
    {m mw evs KinitGamma KdelGamma c_init dsPhi1 stepPhi1 stepPhi2 c_loop2 card1 card2 B_edge : ℕ}
    (hc1 : c_init + dsPhi1 ≤ m * KinitGamma + 52 * m + 45)
    (hshift : stepPhi1 ≤ dsPhi1 + m * KdelGamma + 164 * m + 45 * evs)
    (hc2 : c_loop2 + (stepPhi2 + card2 * B_edge) ≤
      45 * m + 69 * mw + 7 + (stepPhi1 + card1 * B_edge)) :
    (c_init + (c_loop2 + 5 + 1) + 1) + card2 * B_edge ≤
      (m * KinitGamma + m * KdelGamma + 261 * m + 69 * mw + 45 * evs + 60) + card1 * B_edge := by
  omega

/-- Executes one full round (`t2RoundBody`) from `T2LoopState ... r_done` to
`T2LoopState ... (r_done + 1)`, telescoping the edge potential `card * t2EdgeBudget`. -/
lemma task2Round_triple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hp_mid : p.procs[selfBase + 3]? = some (t2MiddleEdgeBody dsBase (selfBase + 4)))
    (hp_drain : p.procs[selfBase + 4]? = some (t2DrainQueueBody dsBase))
    (r_done : ℕ) (emb_prev emb : ℕ → Option Walk) (hCur0 arenaPtr del0 upd0 inn0 : ℕ)
    (hEta_succ : r_done + 1 ≤ eta1Bound ctx.wd inp.J) :
    let γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
    let B_round := inp.J.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ +
      inp.J.m * ⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ +
      261 * inp.J.m + 69 * Task1Input.mwCap impl inp.J + 45 * inp.embVertSum + 60
    PTriple w p
      (fun st Φ => T2LoopState ctx stc r_done emb_prev emb hCur0 arenaPtr del0 upd0 inn0 st ∧
        Φ = (unembeddedSetPure ctx.wd emb).card * t2EdgeBudget impl inp)
      (t2RoundBody selfBase dsBase)
      (pNormalPost fun st' Φ' =>
        ∃ emb' hCur' arenaPtr' del' upd' inn',
          T2LoopState ctx stc (r_done + 1) emb emb' hCur' arenaPtr' del' upd' inn' st' ∧
          Φ' = (unembeddedSetPure ctx.wd emb').card * t2EdgeBudget impl inp)
      (fun _ => B_round) := by
  intro γJ B_round st Φ ω ⟨hLS, hΦ_in⟩
  have hInit := t2Round_init_loop_ptriple ctx stc hSpec r_done emb_prev emb hCur0 arenaPtr del0 upd0 inn0
    hEta_succ
  obtain ⟨o1, st1, c1, Φ1, hr1, hq1, hc1⟩ := hInit st 0 ω ⟨hLS, rfl⟩
  cases o1 with
  | returned _ => exact absurd hq1 (by simp)
  | normal =>
    rcases hq1 with ⟨g1, hStep1, hVcong1, hg1_η, hg1_emb, hg1_prev, hg1_pv, hg1_dr, hg1_q,
      hg1_ic, hg1_ie, hg1_gp, hg1_del, hg1_pdel, hg1_vc, hg1_inn, hg1_ar, hg1_qid,
      _, _, hr1_4, hr1_10, hr1_12, hr1_18, hr1_31, hr1_32, hr1_33, hr1_34, hr1_35, hr1_36,
      hr1_37, hr1_38, hr1_39, hr1_40, hr1_41, hΦ1⟩
    have har1 : stc.nodesEnd ≤ g1.arenaPtr := by rw [hg1_ar]; exact hLS.hAr_lo
    have hO1 : T2OuterInvData ctx stc r_done emb 0 g1
        { st1 with regs := Function.update st1.regs 20 0 } (t2MidPhi ctx stc g1 st1.mem) :=
      { hr4 := by simp (disch := decide) only [Function.update_of_ne, hr1_4]
        hr10 := by simp (disch := decide) only [Function.update_of_ne, hr1_10]
        hr12 := by simp (disch := decide) only [Function.update_of_ne, hr1_12]
        hr20 := by dsimp only; exact Function.update_self _ _ _
        hr31 := by simp (disch := decide) only [Function.update_of_ne, hr1_31]
        hr32 := by simp (disch := decide) only [Function.update_of_ne, hr1_32]
        hr33 := by simp (disch := decide) only [Function.update_of_ne, hr1_33]
        hr34 := by simp (disch := decide) only [Function.update_of_ne, hr1_34]
        hr35 := by simp (disch := decide) only [Function.update_of_ne, hr1_35]
        hr36 := by simp (disch := decide) only [Function.update_of_ne, hr1_36]
        hr37 := by simp (disch := decide) only [Function.update_of_ne, hr1_37]
        hr38 := by simp (disch := decide) only [Function.update_of_ne, hr1_38]
        hr39 := by simp (disch := decide) only [Function.update_of_ne, hr1_39]
        hr40 := by simp (disch := decide) only [Function.update_of_ne, hr1_40]
        hr41 := by simp (disch := decide) only [Function.update_of_ne, hr1_41]
        hr18 := by simp (disch := decide) only [Function.update_of_ne, hr1_18]
        hStep := hStep1
        hVcong := hVcong1
        hη := hg1_η
        hemb_prev := hg1_prev
        hq := hg1_q
        hDr := by rw [hg1_dr, hg1_pv]
        hInitC := hg1_ic
        hInitE := hg1_ie
        har := har1
        hcov_prev := fun _ h => absurd h (Nat.not_lt_zero _)
        hZero := fun _ => hg1_pv
        hPhi := rfl }
    have hL2 := t2Round_loop2_ptriple ctx stc hSpec hp_mid hp_drain (r_done := r_done) (emb₀ := emb)
    obtain ⟨o2, st2, c2, Φ2, hr2, hq2, hc2⟩ := hL2 st1 (t2MidPhi ctx stc g1 st1.mem) ω ⟨g1, hO1⟩
    cases o2 with
    | returned _ => exact absurd hq2 (by simp)
    | normal =>
      rcases hq2 with ⟨g2, hO2⟩
      have hv1_w := (t2_maxWord_scalars ctx stc).2.2.2.1
      have hv1_30_w : inp.v1 + 30 < 2 ^ w := by omega
      have h30_w : 30 < 2 ^ w := by omega
      have he19 := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hO2.hr4)
        (Expr.eval_const h30_w) hv1_30_w)
      change Expr.eval w st2 (t2Ld (.reg 4) (.const 30)) = some (st2.mem (inp.v1 + 30)) at he19
      rw [hO2.hStep.h30] at he19
      let st_fin : State :=
        { st2 with regs := Function.update st2.regs 19 (unembeddedSetPure ctx.wd g2.emb).card }
      have hr19 : Runs w p ω (Stmt.assign 19 (t2Ld (.reg 4) (.const 30))) st2 .normal st_fin 5 :=
        runs_assign_iff.mpr ⟨_, he19, rfl, rfl, rfl⟩
      have hr_tail : Runs w p ω (forRange 20 (.const 0) (.reg 10) (t2OuterCiBody selfBase) ;;
          Stmt.assign 19 (t2Ld (.reg 4) (.const 30))) st1 .normal st_fin (c2 + 5 + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, 5, hr2, hr19, rfl⟩)
      have hr_tot := t2_round_reassoc hr1 hr_tail
      have hLS' := t2Round_math_to_loopState (st_fin := st_fin) ctx stc hO2 rfl
        (fun r hr => Function.update_of_ne hr _ _)
        (by dsimp only [st_fin]; exact Function.update_self _ _ _)
      have hshift : t2StepPhi ctx stc g1 st1.mem ≤
          Φ1 + inp.J.m * ⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ + 164 * inp.J.m + 45 * inp.embVertSum := by
        rw [hΦ1]
        exact t2StepPhi_empty_le ctx stc g1 st1.mem hg1_dr
      have hcost_tot : (c1 + (c2 + 5 + 1) + 1) +
          (unembeddedSetPure ctx.wd g2.emb).card * t2EdgeBudget impl inp ≤
          B_round + Φ := by
        rw [hΦ_in]
        have hstep2_le : t2StepPhi ctx stc g2 st2.mem +
            (unembeddedSetPure ctx.wd g2.emb).card * t2EdgeBudget impl inp = Φ2 :=
          hO2.hPhi.symm
        have hstep1_eq : t2MidPhi ctx stc g1 st1.mem =
            t2StepPhi ctx stc g1 st1.mem + (unembeddedSetPure ctx.wd emb).card * t2EdgeBudget impl inp := by
          simp [t2MidPhi, hg1_emb]
        dsimp only at hc1 hc2
        rw [← hstep2_le, hstep1_eq] at hc2
        exact t2Round_total_cost_arith hc1 hshift hc2
      exact ⟨.normal, st_fin, _, (unembeddedSetPure ctx.wd g2.emb).card * t2EdgeBudget impl inp,
        hr_tot, ⟨g2.emb, g2.hCur, g2.arenaPtr, g2.deleteCountJ, g2.vcongUpdates, g2.innerIters1,
          hLS', rfl⟩, hcost_tot⟩

end MinCostFlow.Spanner

