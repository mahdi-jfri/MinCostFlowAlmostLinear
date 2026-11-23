module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleInv

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Word-RAM execution of `t2MiddleEdgeBody` Stages 1 & 2 (`ds.getPath` and `writeVerts`) -/

/-- Lines 353–366 of `t2MiddleEdgeBody`: loads pointers/endpoints and calls `ds.getPath`. -/
def t2MiddleStage1 (dsBase : ℕ) (cont : Stmt) : Stmt :=
  Stmt.assign 5 (t2Ld (.reg 0) (.const 13)) ;;
  Stmt.assign 6 (t2Ld (.reg 5) (.const 3)) ;;
  Stmt.assign 7 (t2Add (.reg 6) (t2Mul (.const 7) (.reg 1))) ;;
  Stmt.assign 8 (t2Ld (.reg 7) (.const 2)) ;;
  Stmt.assign 9 (t2Ld (.reg 7) (.const 4)) ;;
  Stmt.assign 10 (t2Ld (.reg 0) (.const 14)) ;;
  Stmt.assign 11 (t2Add (t2Ld (.reg 10) (.const 12)) (t2Mul (.const 6) (.reg 1))) ;;
  Stmt.assign 12 (t2Ld (.reg 11) (.const 1)) ;;
  Stmt.assign 13 (t2Ld (.reg 12) (t2Add (.const 2) (t2Mul (.const 2) (.reg 2)))) ;;
  Stmt.assign 14 (t2Ld (.reg 12) (t2Add (.const 3) (t2Mul (.const 2) (.reg 2)))) ;;
  Stmt.assign 15 (t2Ld (.reg 0) (.const 15)) ;;
  Stmt.assign 16 (t2Ld (.reg 15) (.reg 1)) ;;
  Stmt.assign 17 (.reg 4) ;;
  Stmt.call 4 (dsBase + 2) [.reg 16, .reg 13, .reg 14, .reg 4] ;;
  cont

/-- Lines 367–377 of `t2MiddleEdgeBody`: copies lifted vertex ids into `embWJ` arena. -/
def t2MiddleStage2 (cont : Stmt) : Stmt :=
  Stmt.assign 18 (t2Ld (.reg 0) (.const 25)) ;;
  Stmt.assign 19 (.load (.reg 17)) ;;
  Stmt.assign 20 (t2Add (t2Add (.reg 17) (.const 1)) (.reg 19)) ;;
  Stmt.assign 21 (.load (.reg 20)) ;;
  Stmt.store (.reg 18) (.reg 19) ;;
  forRange 22 (.const 0) (.reg 19) (
    Stmt.assign 23 (t2Ld (.reg 17) (t2Add (.const 1) (.reg 22))) ;;
    t2St (.reg 18) (t2Add (.const 1) (.reg 22)) (t2Ld (.reg 8) (.reg 23))
  ) ;;
  Stmt.assign 24 (t2Add (t2Add (.reg 18) (.const 1)) (.reg 19)) ;;
  Stmt.store (.reg 24) (.reg 21) ;;
  cont

lemma t2Middle_stage1_cps {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {ci eL eW : ℕ} (hci : ci < ctx.wd.comps.length)
    (heL : eL < (ctx.wd.comps[ci]'hci).W_sub.m)
    (msf : MiddleStaticFacts ctx stc g₀ ci eL eW memStart)
    (hu_vh : msf.u_loc ∉ (g₀.states ci).Vhat) (hv_vh : msf.v_loc ∉ (g₀.states ci).Vhat)
    (st : State) (hr0 : st.regs 0 = inp.v1) (hr1 : st.regs 1 = ci) (hr2 : st.regs 2 = eL)
    (hr3 : st.regs 3 = eW) (hr4 : st.regs 4 = g₀.hCur) (hmem : st.mem = memStart)
    (cont : Stmt) (ω : ℕ → Bool)
    (Q : Outcome → State → ℕ → ℕ → Prop)
    (hcont : ∀ (o_gp : Outcome) (st_gp : State) (c_gp : ℕ)
        (rep' : impl.pathDS.R.τ) (P_sub : Walk),
      g₀.hCur ≤ o_gp.value →
      o_gp.value ≤ g₀.hCur +
        impl.pathDS.params.querySpace ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
          (ctx.wd.comps[ci]'hci).J_sub.n (ctx.wd.comps[ci]'hci).J_sub.m ctx.wd.J0_strip.m →
      o_gp.value ≤ Task2Input.maxHeapEnd impl inp →
      (∀ a < stc.dsBaseAddr, st_gp.mem a = memStart a) →
      WalkAt st_gp.mem g₀.hCur P_sub →
      P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub msf.u_loc msf.v_loc →
      P_sub.verts.Nodup →
      (∀ b ∈ P_sub.edges, b ∉ (g₀.states ci).deleted) →
      (∀ y ∈ P_sub.verts, y ∉ (g₀.states ci).Vhat) →
      (P_sub.edges.length : ℝ) ≤
        impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
          ctx.wd.J0_strip.m →
      P_sub.edges.length ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params →
      DSArrayAt impl.pathDS ctx.wd.comps ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
        ctx.wd.J0_strip.m w stc.dsBaseAddr (inp.dsHandlesAddr ctx.wd.W.m) o_gp.value st_gp.mem
        ctx.wd.comps.length g₀.states (Function.update g₀.reps ci rep') →
      c_gp + dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
          (Function.update g₀.reps ci rep') st_gp.mem ≤
        ⌈impl.pathDS.params.K_query * impl.pathDS.params.γ_query
          ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec) ctx.wd.J0_strip.m⌉₊ +
          dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length g₀.reps memStart →
      ∀ (st_post : State),
        st_post.mem = st_gp.mem →
        st_post.regs 0 = inp.v1 → st_post.regs 1 = ci → st_post.regs 2 = eL →
        st_post.regs 3 = eW → st_post.regs 4 = o_gp.value →
        st_post.regs 8 = msf.cVertsPtr → st_post.regs 9 = msf.cJOrigPtr →
        st_post.regs 10 = ctx.wInp.h → st_post.regs 17 = g₀.hCur →
        ∃ (o : Outcome) (stF : State) (c_cont : ℕ),
          Runs w p ω cont st_post o stF c_cont ∧
          Q o stF c_gp c_cont) :
    ∃ (o : Outcome) (stF : State) (c_gp c_cont c_tot : ℕ),
      Runs w p ω (t2MiddleStage1 dsBase cont) st o stF c_tot ∧
      Q o stF c_gp c_cont ∧
      c_tot ≤ c_gp + c_cont + 109 := by
  have db := msf.db
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc; have _ := db.h_mhe
  have hmwb := db.h_mwb
  have hchain := t2_prep_chain_bounds ctx
  have ⟨_, _, _, _, _, _, _, hstOut⟩ := ctx.agrees_preserves_static hS.agr_pre
  have ⟨_, _, _, _, _, _, _, _, _, _, _, ha1, _, ha3, _, hce, _⟩ := hstOut
  have hprep_lt : ctx.wInp.prep.h + 3 < 2 ^ w := by omega
  have haComps_w : msf.aComps + 7 * ci < 2 ^ w := by have := msf.haComps_lt; omega
  have haC_2w : msf.aComps + 7 * ci + 2 < 2 ^ w := by have := msf.haComps_lt; omega
  have haC_4w : msf.aComps + 7 * ci + 4 < 2 ^ w := by have := msf.haComps_lt; omega
  have hwH12_w : ctx.wInp.h + 12 < 2 ^ w := by
    have : ctx.wInp.h + 20 ≤ msf.aCompExt := by rwa [← msf.haCompExt_ptr]
    have : msf.wWNumAddr + ctx.wd.W.m ≤ inp.v1 := msf.hwWNum_lt
    have : msf.aCompExt + 6 * ci + 5 < msf.wWNumAddr := msf.haCompExt_lt
    omega
  have haCE_6w : 6 * ci < 2 ^ w := msf.h6ci_w
  have haCE_w : msf.aCompExt + 6 * ci < 2 ^ w := by
    have := msf.haCompExt_lt; have := msf.hwWNum_lt; omega
  have haCE_1w : msf.aCompExt + 6 * ci + 1 < 2 ^ w := by
    have := msf.haCompExt_lt; have := msf.hwWNum_lt; omega
  have hwSub_w : msf.wSubPtr + (3 + 2 * eL) < 2 ^ w := by
    have hce_ci := hce ci hci
    have hsub_le : msf.wSubPtr + (2 + 2 * (ctx.wd.comps[ci]'hci).W_sub.m) ≤ memStart (ctx.wInp.h + 13) := by
      rw [← msf.hwSub_ptr, ← msf.haCompExt_ptr]
      simpa only [List.getD_eq_getElem _ _ hci] using hce_ci.2.2.2.2.2.2.2
    have hww_eq : msf.wWNumAddr = memStart (ctx.wInp.h + 13) + (2 + 2 * ctx.wd.W.m) := by
      rw [← msf.hwWNum_ptr]; exact ha3
    have := msf.hwWNum_lt
    omega
  have hhdl_w : inp.dsHandlesAddr ctx.wd.W.m + ci < 2 ^ w := by omega
  set s5 := { st with regs := Function.update st.regs 5 ctx.wInp.prep.h }
  have hr5 : Runs w p ω (Stmt.assign 5 (t2Ld (.reg 0) (.const 13))) st .normal s5 5 := by
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by omega : 13 < 2 ^ w)) (by omega)
    exact runs_assign_iff.mpr ⟨ctx.wInp.prep.h,
      by simpa only [t2Ld, hmem, msf.hprep13] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s6 := { s5 with regs := Function.update s5.regs 6 msf.aComps }
  have hr6 : Runs w p ω (Stmt.assign 6 (t2Ld (.reg 5) (.const 3))) s5 .normal s6 5 := by
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s5.regs 5 = ctx.wInp.prep.h by simp [s5]))
      (Expr.eval_const (by omega : 3 < 2 ^ w)) hprep_lt
    exact runs_assign_iff.mpr ⟨msf.aComps,
      by simpa only [t2Ld, s5, hmem, msf.haComps_ptr] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s7 := { s6 with regs := Function.update s6.regs 7 (msf.aComps + 7 * ci) }
  have hr7 : Runs w p ω (Stmt.assign 7 (t2Add (.reg 6) (t2Mul (.const 7) (.reg 1)))) s6 .normal s7 6 := by
    have hm := Expr.eval_mul (w := w) (Expr.eval_const (by omega : 7 < 2 ^ w))
      (Expr.eval_reg_of_eq (show s6.regs 1 = ci by dsimp only [s6, s5]; rw [Function.update_of_ne (by omega)]; exact hr1))
      msf.h7ci_w
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s6.regs 6 = msf.aComps by simp [s6])) hm haComps_w
    exact runs_assign_iff.mpr ⟨msf.aComps + 7 * ci, by simpa only [t2Add, t2Mul] using ha,
      rfl, rfl, by simp [Expr.size]⟩
  set s8 := { s7 with regs := Function.update s7.regs 8 msf.cVertsPtr }
  have hr8 : Runs w p ω (Stmt.assign 8 (t2Ld (.reg 7) (.const 2))) s7 .normal s8 5 := by
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s7.regs 7 = msf.aComps + 7 * ci by simp [s7]))
      (Expr.eval_const (by omega : 2 < 2 ^ w)) haC_2w
    exact runs_assign_iff.mpr ⟨msf.cVertsPtr,
      by simpa only [t2Ld, s7, s6, s5, hmem, msf.hcVerts_ptr] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s9 := { s8 with regs := Function.update s8.regs 9 msf.cJOrigPtr }
  have hr9 : Runs w p ω (Stmt.assign 9 (t2Ld (.reg 7) (.const 4))) s8 .normal s9 5 := by
    have ha := Expr.eval_add (w := w)
      (Expr.eval_reg_of_eq (show s8.regs 7 = msf.aComps + 7 * ci by dsimp only [s8]; rw [Function.update_of_ne (by omega)]; simp [s7]))
      (Expr.eval_const (by omega : 4 < 2 ^ w)) haC_4w
    exact runs_assign_iff.mpr ⟨msf.cJOrigPtr,
      by simpa only [t2Ld, s8, s7, s6, s5, hmem, msf.hcJOrig_ptr] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s10 := { s9 with regs := Function.update s9.regs 10 ctx.wInp.h }
  have hr10 : Runs w p ω (Stmt.assign 10 (t2Ld (.reg 0) (.const 14))) s9 .normal s10 5 := by
    have h0 : s9.regs 0 = inp.v1 := by dsimp only [s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr0]
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq h0) (Expr.eval_const (by omega : 14 < 2 ^ w)) (by omega)
    exact runs_assign_iff.mpr ⟨ctx.wInp.h,
      by simpa only [t2Ld, s9, s8, s7, s6, s5, hmem, msf.hwH14] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s11 := { s10 with regs := Function.update s10.regs 11 (msf.aCompExt + 6 * ci) }
  have hr11 : Runs w p ω (Stmt.assign 11 (t2Add (t2Ld (.reg 10) (.const 12)) (t2Mul (.const 6) (.reg 1)))) s10 .normal s11 9 := by
    have ha1 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s10.regs 10 = ctx.wInp.h by simp [s10]))
      (Expr.eval_const (by omega : 12 < 2 ^ w)) hwH12_w
    have hl1 : (t2Ld (.reg 10) (.const 12)).eval w s10 = some msf.aCompExt := by
      simpa only [t2Ld, s10, s9, s8, s7, s6, s5, hmem, msf.haCompExt_ptr] using Expr.eval_load ha1
    have h1 : s10.regs 1 = ci := by dsimp only [s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr1]
    have hm1 := Expr.eval_mul (w := w) (Expr.eval_const (by omega : 6 < 2 ^ w)) (Expr.eval_reg_of_eq h1) haCE_6w
    have ha2 := Expr.eval_add (w := w) hl1 hm1 haCE_w
    exact runs_assign_iff.mpr ⟨msf.aCompExt + 6 * ci, by simpa only [t2Add, t2Mul] using ha2,
      rfl, rfl, by simp [Expr.size]⟩
  set s12 := { s11 with regs := Function.update s11.regs 12 msf.wSubPtr }
  have hr12 : Runs w p ω (Stmt.assign 12 (t2Ld (.reg 11) (.const 1))) s11 .normal s12 5 := by
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s11.regs 11 = msf.aCompExt + 6 * ci by simp [s11]))
      (Expr.eval_const (by omega : 1 < 2 ^ w)) haCE_1w
    exact runs_assign_iff.mpr ⟨msf.wSubPtr,
      by simpa only [t2Ld, s11, s10, s9, s8, s7, s6, s5, hmem, msf.hwSub_ptr] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s13 := { s12 with regs := Function.update s12.regs 13 msf.u_loc }
  have hr13 : Runs w p ω (Stmt.assign 13 (t2Ld (.reg 12) (t2Add (.const 2) (t2Mul (.const 2) (.reg 2))))) s12 .normal s13 9 := by
    have h2 : s12.regs 2 = eL := by dsimp only [s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr2]
    have hm1 := Expr.eval_mul (w := w) (Expr.eval_const (by omega : 2 < 2 ^ w)) (Expr.eval_reg_of_eq h2) (by omega)
    have ha1 := Expr.eval_add (w := w) (Expr.eval_const (by omega : 2 < 2 ^ w)) hm1 (by omega)
    have ha2 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s12.regs 12 = msf.wSubPtr by simp [s12])) ha1 (by omega)
    exact runs_assign_iff.mpr ⟨msf.u_loc,
      by simpa only [t2Ld, t2Add, t2Mul, s12, s11, s10, s9, s8, s7, s6, s5, hmem, msf.hu_mem] using Expr.eval_load ha2,
      rfl, rfl, by simp [Expr.size]⟩
  set s14 := { s13 with regs := Function.update s13.regs 14 msf.v_loc }
  have hr14 : Runs w p ω (Stmt.assign 14 (t2Ld (.reg 12) (t2Add (.const 3) (t2Mul (.const 2) (.reg 2))))) s13 .normal s14 9 := by
    have h2 : s13.regs 2 = eL := by dsimp only [s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr2]
    have h12 : s13.regs 12 = msf.wSubPtr := by dsimp only [s13]; rw [Function.update_of_ne (by omega)]; simp [s12]
    have hm1 := Expr.eval_mul (w := w) (Expr.eval_const (by omega : 2 < 2 ^ w)) (Expr.eval_reg_of_eq h2) (by omega)
    have ha1 := Expr.eval_add (w := w) (Expr.eval_const (by omega : 3 < 2 ^ w)) hm1 (by omega)
    have ha2 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq h12) ha1 hwSub_w
    exact runs_assign_iff.mpr ⟨msf.v_loc,
      by simpa only [t2Ld, t2Add, t2Mul, s13, s12, s11, s10, s9, s8, s7, s6, s5, hmem, msf.hv_mem] using Expr.eval_load ha2,
      rfl, rfl, by simp [Expr.size]⟩
  set s15 := { s14 with regs := Function.update s14.regs 15 (inp.dsHandlesAddr ctx.wd.W.m) }
  have hr15 : Runs w p ω (Stmt.assign 15 (t2Ld (.reg 0) (.const 15))) s14 .normal s15 5 := by
    have h0 : s14.regs 0 = inp.v1 := by dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr0]
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq h0) (Expr.eval_const (by omega : 15 < 2 ^ w)) (by omega)
    exact runs_assign_iff.mpr ⟨inp.dsHandlesAddr ctx.wd.W.m,
      by simpa only [t2Ld, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, hmem, hS.h15] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s16 := { s15 with regs := Function.update s15.regs 16 (memStart (inp.dsHandlesAddr ctx.wd.W.m + ci)) }
  have hr16 : Runs w p ω (Stmt.assign 16 (t2Ld (.reg 15) (.reg 1))) s15 .normal s16 5 := by
    have h1 : s15.regs 1 = ci := by dsimp only [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr1]
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq (show s15.regs 15 = inp.dsHandlesAddr ctx.wd.W.m by simp [s15]))
      (Expr.eval_reg_of_eq h1) hhdl_w
    exact runs_assign_iff.mpr ⟨memStart (inp.dsHandlesAddr ctx.wd.W.m + ci),
      by simpa only [t2Ld, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, hmem] using Expr.eval_load ha,
      rfl, rfl, by simp [Expr.size]⟩
  set s17 := { s16 with regs := Function.update s16.regs 17 g₀.hCur }
  have hr17 : Runs w p ω (Stmt.assign 17 (.reg 4)) s16 .normal s17 2 := by
    have h4 : s16.regs 4 = g₀.hCur := by dsimp only [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr4]
    exact runs_assign_iff.mpr ⟨g₀.hCur, Expr.eval_reg_of_eq h4, rfl, rfl, by simp [Expr.size]⟩
  have hG_eq : (g₀.states ci).G = (ctx.wd.comps[ci]'hci).J_sub := by
    rw [(hS.hDS.at_ci ci hci).2.2.2.2.1, List.getD_eq_getElem _ _ hci]
  have hu_lt_n : msf.u_loc < (ctx.wd.comps[ci]'hci).J_sub.n := by
    have h := msf.hu_lt; rw [List.getD_eq_getElem _ _ hci] at h; exact h
  have hv_lt_n : msf.v_loc < (ctx.wd.comps[ci]'hci).J_sub.n := by
    have h := msf.hv_lt; rw [List.getD_eq_getElem _ _ hci] at h; exact h
  have hu_in : msf.u_loc ∈ (g₀.states ci).G.verts \ (g₀.states ci).Vhat := by
    refine Finset.mem_sdiff.mpr ⟨?_, hu_vh⟩
    rw [hG_eq, Graph.verts, Finset.mem_range]; exact hu_lt_n
  have hv_in : msf.v_loc ∈ (g₀.states ci).G.verts \ (g₀.states ci).Vhat := by
    refine Finset.mem_sdiff.mpr ⟨?_, hv_vh⟩
    rw [hG_eq, Graph.verts, Finset.mem_range]; exact hv_lt_n
  have hcw_ci : impl.pathDS.params.cw * (Nat.log 2 ((ctx.wd.comps[ci]'hci).J_sub.n +
      (ctx.wd.comps[ci]'hci).J_sub.m + ctx.wInp.prep.phiDen_dec + ctx.wd.J0_strip.m +
      ⌈impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
        ctx.wd.J0_strip.m⌉₊ + 2) + 1) ≤ w := by
    simpa only [List.getD_eq_getElem _ _ hci] using msf.hcw_ci
  have hpow_n : (ctx.wd.comps[ci]'hci).J_sub.n < 2 ^ w := by
    let L := Nat.log 2 ((ctx.wd.comps[ci]'hci).J_sub.n + (ctx.wd.comps[ci]'hci).J_sub.m +
        ctx.wInp.prep.phiDen_dec + ctx.wd.J0_strip.m +
        ⌈impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
          ctx.wd.J0_strip.m⌉₊ + 2)
    have hmul : L + 1 ≤ impl.pathDS.params.cw * (L + 1) := by
      simpa using Nat.mul_le_mul_right (L + 1) impl.pathDS.params.hcw_pos
    have h1 : L + 1 ≤ w := le_trans hmul hcw_ci
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
      ((ctx.wd.comps[ci]'hci).J_sub.n + (ctx.wd.comps[ci]'hci).J_sub.m +
        ctx.wInp.prep.phiDen_dec + ctx.wd.J0_strip.m +
        ⌈impl.pathDS.params.γ_ExpPath ((ctx.wInp.prep.phiNum_dec : ℝ) / ctx.wInp.prep.phiDen_dec)
          ctx.wd.J0_strip.m⌉₊ + 2)
    have h3 : 2 ^ (L + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) h1
    change _ < 2 ^ (L + 1) at h2
    exact lt_trans (by omega) (lt_of_lt_of_le h2 h3)
  have hu_w : msf.u_loc < 2 ^ w := lt_trans hu_lt_n hpow_n
  have hv_w : msf.v_loc < 2 ^ w := lt_trans hv_lt_n hpow_n
  have hhCur_w : g₀.hCur < 2 ^ w := by have := msf.hCur_max; have := msf.hmax_3; omega
  have hSpace_w : g₀.hCur + impl.pathDS.params.querySpace ctx.wInp.prep.phiNum_dec
      ctx.wInp.prep.phiDen_dec (ctx.wd.comps[ci]'hci).J_sub.n (ctx.wd.comps[ci]'hci).J_sub.m
      ctx.wd.J0_strip.m < 2 ^ w := by
    have := msf.hCur_space; rw [List.getD_eq_getElem _ _ hci] at this
    have := msf.hmax_3; omega
  obtain ⟨body_gp, o_gp, st_gp, c_gp, rep', P_sub, hp_gp, hr_gp, hgp_ge, hgp_le,
      hgp_below, hwk_sub, hcw_sub, hPsub_nd, hPsub_undel, hPsub_vh, hPsub_len, hDS_gp, hgp_phi⟩ :=
    hS.hDS.call_getPath (ω := ω) (pos := s17.pos) hSpec hci le_rfl (by omega)
      hu_in hv_in hu_w hv_w hhCur_w hcw_ci hSpace_w
  set st_post : State := { st_gp with regs := Function.update s17.regs 4 o_gp.value }
  have hr_call : Runs w p ω (Stmt.call 4 (dsBase + 2) [.reg 16, .reg 13, .reg 14, .reg 4]) s17 .normal
      st_post (4 + c_gp + 1) := by
    have e16 : (Expr.reg 16).eval w s17 = some (memStart (inp.dsHandlesAddr ctx.wd.W.m + ci)) :=
      Expr.eval_reg_of_eq (by dsimp only [s17]; rw [Function.update_of_ne (by omega)]; simp [s16])
    have e13 : (Expr.reg 13).eval w s17 = some msf.u_loc :=
      Expr.eval_reg_of_eq (by dsimp only [s17, s16, s15, s14]; simp [Function.update_of_ne, s13])
    have e14 : (Expr.reg 14).eval w s17 = some msf.v_loc :=
      Expr.eval_reg_of_eq (by dsimp only [s17, s16, s15]; simp [Function.update_of_ne, s14])
    have e4 : (Expr.reg 4).eval w s17 = some g₀.hCur :=
      Expr.eval_reg_of_eq (by dsimp only [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr4])
    have hs17_mem : s17.mem = memStart := by
      dsimp only [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; exact hmem
    exact runs_call_iff.mpr ⟨[memStart (inp.dsHandlesAddr ctx.wd.W.m + ci), msf.u_loc, msf.v_loc, g₀.hCur],
      body_gp, o_gp, st_gp, c_gp, by simp [evalArgs, e16, e13, e14, e4],
      hp_gp, by rw [hs17_mem]; exact hr_gp, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hgp_hi : o_gp.value ≤ Task2Input.maxHeapEnd impl inp :=
    le_trans hgp_le (by simpa only [List.getD_eq_getElem _ _ hci] using msf.hCur_space)
  have hPsub_le_γ : P_sub.edges.length ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params := by
    have := ctx.ds_bounds.2.2.2.2.2.2.2.2.2
    exact_mod_cast le_trans hPsub_len this
  obtain ⟨o, stF, c_cont, hr_cont, hQ⟩ := hcont o_gp st_gp c_gp rep' P_sub
    hgp_ge hgp_le hgp_hi hgp_below hwk_sub hcw_sub hPsub_nd hPsub_undel hPsub_vh hPsub_len hPsub_le_γ
    hDS_gp hgp_phi st_post rfl
    (by dsimp only [st_post, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr0])
    (by dsimp only [st_post, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr1])
    (by dsimp only [st_post, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr2])
    (by dsimp only [st_post, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne, hr3])
    (by dsimp only [st_post]; exact Function.update_self _ _ _)
    (by dsimp only [st_post, s17, s16, s15, s14, s13, s12, s11, s10, s9]; simp [Function.update_of_ne, s8])
    (by dsimp only [st_post, s17, s16, s15, s14, s13, s12, s11, s10]; simp [Function.update_of_ne, s9])
    (by dsimp only [st_post, s17, s16, s15, s14, s13, s12, s11]; simp [Function.update_of_ne, s10])
    (by dsimp only [st_post]; rw [Function.update_of_ne (by omega)]; simp [s17])
  refine ⟨o, stF, c_gp, c_cont, _,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, hr5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, hr6,
        runs_seq_iff.mpr (Or.inr ⟨s7, 6, _, hr7,
          runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, hr8,
            runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, hr9,
              runs_seq_iff.mpr (Or.inr ⟨s10, 5, _, hr10,
                runs_seq_iff.mpr (Or.inr ⟨s11, 9, _, hr11,
                  runs_seq_iff.mpr (Or.inr ⟨s12, 5, _, hr12,
                    runs_seq_iff.mpr (Or.inr ⟨s13, 9, _, hr13,
                      runs_seq_iff.mpr (Or.inr ⟨s14, 9, _, hr14,
                        runs_seq_iff.mpr (Or.inr ⟨s15, 5, _, hr15,
                          runs_seq_iff.mpr (Or.inr ⟨s16, 5, _, hr16,
                            runs_seq_iff.mpr (Or.inr ⟨s17, 2, _, hr17,
                              runs_seq_iff.mpr (Or.inr ⟨st_post, 4 + c_gp + 1, c_cont, hr_call, hr_cont, rfl⟩),
                              rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    hQ, by omega⟩

lemma t2Middle_stage2_cps {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {g₀ : T2Ghost impl.pathDS} {memStart mem_gp : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    (har_lo : stc.nodesEnd ≤ g₀.arenaPtr)
    {ci eL eW hCurNew u_loc v_loc : ℕ} {P_sub : Walk}
    (hci : ci < ctx.wd.comps.length)
    (msf : MiddleStaticFacts ctx stc g₀ ci eL eW memStart)
    (hcw_sub : P_sub.IsWalk (ctx.wd.comps[ci]'hci).J_sub u_loc v_loc)
    (hPsub_nd : P_sub.verts.Nodup)
    (hPsub_le_γ : P_sub.edges.length ≤ ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params)
    (hwk_sub : WalkAt mem_gp g₀.hCur P_sub) (hz_new : WordRAM.ZeroFrom mem_gp hCurNew)
    (hCur_le : g₀.hCur ≤ hCurNew) (hCur_hi : hCurNew ≤ Task2Input.maxHeapEnd impl inp)
    (hgp_below : ∀ a < stc.dsBaseAddr, mem_gp a = memStart a)
    (st : State) (hmem : st.mem = mem_gp)
    (hr0 : st.regs 0 = inp.v1) (hr1 : st.regs 1 = ci)
    (hr4 : st.regs 4 = hCurNew)
    (hr8 : st.regs 8 = msf.cVertsPtr)
    (hr17 : st.regs 17 = g₀.hCur)
    (cont : Stmt) (ω : ℕ → Bool)
    (Q : Outcome → State → ℕ → ℕ → Prop)
    (hcont : ∀ (st_post : State) (c_wv : ℕ),
      c_wv ≤ P_sub.verts.length * 27 + 7 →
      (∀ r ≤ 21, st_post.regs r =
        if r = 18 then g₀.arenaPtr else if r = 19 then P_sub.verts.length
        else if r = 20 then g₀.hCur + 1 + P_sub.verts.length
        else if r = 21 then P_sub.edges.length else st.regs r) →
      st_post.regs 24 = g₀.arenaPtr + 1 + P_sub.verts.length →
      st_post.mem g₀.arenaPtr = (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.length →
      (∀ j < P_sub.verts.length, st_post.mem (g₀.arenaPtr + 1 + j) =
        (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.getD j 0) →
      st_post.mem (g₀.arenaPtr + 1 + P_sub.verts.length) =
        (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).edges.length →
      (∀ a, ¬(g₀.arenaPtr ≤ a ∧ a ≤ g₀.arenaPtr + 1 + P_sub.verts.length) →
        st_post.mem a = mem_gp a) →
      ∃ (o : Outcome) (stF : State) (c_cont : ℕ),
        Runs w p ω cont st_post o stF c_cont ∧ Q o stF c_wv c_cont) :
    ∃ (o : Outcome) (stF : State) (c_wv c_cont c_tot : ℕ),
      Runs w p ω (t2MiddleStage2 cont) st o stF c_tot ∧
      Q o stF c_wv c_cont ∧
      c_tot ≤ c_wv + c_cont + 38 := by
  have db := msf.db
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo; have _ := db.h_nds; have _ := db.h_dsc; have _ := db.h_stc; have _ := db.h_mhe
  have hmwb := db.h_mwb; have hw1 := db.h_w1; have hmax3 := msf.hmax_3
  have hds_hCur : stc.dsBaseAddr ≤ g₀.hCur := by have := hS.hDS.h_ge; exact this
  have hwk_bd := t2_walkAt_add_le hcw_sub hPsub_nd hwk_sub hz_new hCur_le
  have hy_sub : ∀ y ∈ P_sub.verts, y < (ctx.wd.comps[ci]'hci).J_sub.n := fun y hy =>
    Walk.isWalk_verts_lt (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.1 hcw_sub y hy
  have har_hi : g₀.arenaPtr + 2 + P_sub.verts.length + P_sub.edges.length ≤ stc.dsBaseAddr := by
    have := msf.har_next
    omega
  have hv1_w : inp.v1 + 25 < 2 ^ w := by omega
  have hCurNew_w : hCurNew < 2 ^ w := by omega
  have hhCur_v_w : g₀.hCur + 1 + P_sub.verts.length < 2 ^ w := by omega
  have har_v_w : g₀.arenaPtr + 1 + P_sub.verts.length < 2 ^ w := by omega
  have hm_25 : st.mem (inp.v1 + 25) = g₀.arenaPtr := by
    rw [hmem, hgp_below _ (by omega), hS.h25]
  have hc_verts_lt : msf.cVertsPtr + (ctx.wd.comps[ci]'hci).verts.length ≤ ctx.wInp.prep.hEnd := by
    have hlen_r := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
    have hci_r : ci < ctx.wInp.prep.rawComps.length := by
      simpa [T2Ctx.wd, WitnessCoreInput.mkWitnessData, hlen_r] using hci
    have hcd := (ctx.agrees_preserves_static hS.agr_pre).2.2.2.2.2.1
    have hc_bang : ctx.wInp.prep.rawComps[ci]! = ctx.wInp.prep.rawComps[ci] := by simp [hci_r]
    have ha1 := (ctx.agrees_preserves_static hS.agr_pre).2.2.2.2.1.2.2.2.2.1
    have haC : msf.aComps = ctx.wInp.prep.aComps := by rw [← msf.haComps_ptr]; exact ha1
    have hcV_eq : msf.cVertsPtr = ctx.wInp.prep.cVertsPtr ci := by
      rw [← msf.hcVerts_ptr, haC]; exact (hcd ci hci_r).2.2.1
    have hvl_eq : (ctx.wd.comps[ci]'hci).verts.length = ctx.wInp.prep.rawComps[ci]!.2.length := by
      have hp := ctx.hw_okW.comp_props ci hci
      have hts := (t2_prep_cJSub_m_eq ctx hci).2.2
      rw [hp.2.2.2.2.1, vertsOf, Finset.length_sort, hts, hc_bang]
    have hbd := cVertsPtr_add_le_h ctx.hstat.toValid_zeroTail hci_r
    have hch := t2_prep_chain_bounds ctx
    omega
  have hEnd_lo : ctx.wInp.prep.hEnd ≤ stc.nodesEnd := by
    have := (t2_prep_chain_bounds ctx).2.2.2; omega
  have hcV_list : ListAt (Function.update mem_gp g₀.arenaPtr P_sub.verts.length) msf.cVertsPtr
      (ctx.wd.comps[ci]'hci).verts := by
    intro y hy
    rw [Function.update_of_ne (by omega), hgp_below _ (by omega)]
    have h0 := msf.hcVerts_list
    rw [List.getD_eq_getElem _ _ hci] at h0
    exact h0 y hy
  set s18 := { st with regs := Function.update st.regs 18 g₀.arenaPtr }
  have hr18 : Runs w p ω (Stmt.assign 18 (t2Ld (.reg 0) (.const 25))) st .normal s18 5 := by
    have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by omega : 25 < 2 ^ w)) hv1_w
    exact runs_assign_iff.mpr ⟨g₀.arenaPtr, by simpa only [t2Ld, hm_25] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
  set s19 := { s18 with regs := Function.update s18.regs 19 P_sub.verts.length }
  have hr19 : Runs w p ω (Stmt.assign 19 (.load (.reg 17))) s18 .normal s19 3 := by
    have h17' : s18.regs 17 = g₀.hCur := by dsimp only [s18]; rw [Function.update_of_ne (by omega)]; exact hr17
    have hm17 : s18.mem g₀.hCur = P_sub.verts.length := by rw [show s18.mem = mem_gp from hmem]; exact hwk_sub.verts_len
    exact runs_assign_iff.mpr ⟨P_sub.verts.length, by simpa only [hm17] using Expr.eval_load (Expr.eval_reg_of_eq h17'),
      rfl, rfl, by simp [Expr.size]⟩
  set s20 := { s19 with regs := Function.update s19.regs 20 (g₀.hCur + 1 + P_sub.verts.length) }
  have hr20 : Runs w p ω (Stmt.assign 20 (t2Add (t2Add (.reg 17) (.const 1)) (.reg 19))) s19 .normal s20 6 := by
    have h17' : s19.regs 17 = g₀.hCur := by dsimp only [s19, s18]; simp [Function.update_of_ne, hr17]
    have ha1 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq h17') (Expr.eval_const hw1) (by omega)
    have ha2 := Expr.eval_add (w := w) ha1 (Expr.eval_reg_of_eq (show s19.regs 19 = P_sub.verts.length by simp [s19])) hhCur_v_w
    exact runs_assign_iff.mpr ⟨g₀.hCur + 1 + P_sub.verts.length, by simpa only [t2Add] using ha2,
      rfl, rfl, by simp [Expr.size]⟩
  set s21 := { s20 with regs := Function.update s20.regs 21 P_sub.edges.length }
  have hr21 : Runs w p ω (Stmt.assign 21 (.load (.reg 20))) s20 .normal s21 3 := by
    have hm20 : s20.mem (g₀.hCur + 1 + P_sub.verts.length) = P_sub.edges.length := by
      rw [show s20.mem = mem_gp from hmem]; exact hwk_sub.edges_len
    exact runs_assign_iff.mpr ⟨P_sub.edges.length,
      by simpa only [hm20] using Expr.eval_load (Expr.eval_reg_of_eq (show s20.regs 20 = g₀.hCur + 1 + P_sub.verts.length by simp [s20])),
      rfl, rfl, by simp [Expr.size]⟩
  set m1 := Function.update mem_gp g₀.arenaPtr P_sub.verts.length
  set sm1 : State := { s21 with mem := m1 }
  have hm1_st : Runs w p ω (Stmt.store (.reg 18) (.reg 19)) s21 .normal sm1 3 := by
    have h18' : s21.regs 18 = g₀.arenaPtr := by dsimp only [s21, s20, s19]; simp [Function.update_of_ne, s18]
    have h19' : s21.regs 19 = P_sub.verts.length := by dsimp only [s21, s20]; simp [Function.update_of_ne, s19]
    have hs21_eq : sm1 = { s21 with mem := Function.update s21.mem g₀.arenaPtr P_sub.verts.length } := by
      dsimp only [sm1, m1, s21, s20, s19, s18]; rw [hmem]
    exact runs_store_iff.mpr ⟨g₀.arenaPtr, P_sub.verts.length, Expr.eval_reg_of_eq h18', Expr.eval_reg_of_eq h19',
      rfl, hs21_eq, by simp [Expr.size]⟩
  have hwk_m1 : WalkAt m1 g₀.hCur P_sub := by
    rw [walkAt_iff]
    exact ⟨by simp [m1, Function.update_of_ne (by omega : g₀.hCur ≠ g₀.arenaPtr), hwk_sub.verts_len],
      fun k hk => by simp [m1, Function.update_of_ne (by omega : g₀.hCur + 1 + k ≠ g₀.arenaPtr), hwk_sub.verts_listAt k hk],
      by simp [m1, Function.update_of_ne (by omega : g₀.hCur + 1 + P_sub.verts.length ≠ g₀.arenaPtr), hwk_sub.edges_len],
      fun k hk => by simp [m1, Function.update_of_ne (by omega : g₀.hCur + 2 + P_sub.verts.length + k ≠ g₀.arenaPtr), hwk_sub.edges_listAt k hk]⟩
  have hz_m1 : WordRAM.ZeroFrom m1 hCurNew := fun a ha => by
    simp only [m1, Function.update_of_ne (by omega : a ≠ g₀.arenaPtr)]; exact hz_new a ha
  obtain ⟨st_wv, c_wv, hr_wv, hr_wv_regs, ha_wv_mem, hv_wv_mem, hc_wv⟩ :=
    t2Middle_writeVerts_forRange (p := p) ctx stc hci hcw_sub hPsub_nd hy_sub m1 hwk_m1 hz_m1 hCur_le hCur_hi
      hmax3 hmwb hw1 hcV_list hc_verts_lt hEnd_lo har_lo har_hi hds_hCur (le_trans db.h_dsc db.h_stc)
      s21.regs
      (by dsimp only [s21, s20, s19, s18]; simp [Function.update_of_ne, hr8])
      (by dsimp only [s21, s20, s19, s18]; simp [Function.update_of_ne, hr17])
      (by dsimp only [s21, s20, s19]; simp [Function.update_of_ne, s18])
      (by dsimp only [s21, s20]; simp [Function.update_of_ne, s19])
      sm1.pos ω
  set s24 := { st_wv with regs := Function.update st_wv.regs 24 (g₀.arenaPtr + 1 + P_sub.verts.length) }
  have hr24 : Runs w p ω (Stmt.assign 24 (t2Add (t2Add (.reg 18) (.const 1)) (.reg 19))) st_wv .normal s24 6 := by
    have h18' : st_wv.regs 18 = g₀.arenaPtr := (hr_wv_regs 18 (by omega)).trans (by dsimp only [s21, s20, s19]; simp [Function.update_of_ne, s18])
    have h19' : st_wv.regs 19 = P_sub.verts.length := (hr_wv_regs 19 (by omega)).trans (by dsimp only [s21, s20]; simp [Function.update_of_ne, s19])
    have ha1 := Expr.eval_add (w := w) (Expr.eval_reg_of_eq h18') (Expr.eval_const hw1) (by omega)
    have ha2 := Expr.eval_add (w := w) ha1 (Expr.eval_reg_of_eq h19') har_v_w
    exact runs_assign_iff.mpr ⟨g₀.arenaPtr + 1 + P_sub.verts.length, by simpa only [t2Add] using ha2, rfl, rfl, by simp [Expr.size]⟩
  set m2 := Function.update st_wv.mem (g₀.arenaPtr + 1 + P_sub.verts.length) P_sub.edges.length
  set s25 : State := { s24 with mem := m2 }
  have hm2_st : Runs w p ω (Stmt.store (.reg 24) (.reg 21)) s24 .normal s25 3 := by
    have h21' : s24.regs 21 = P_sub.edges.length := by
      dsimp only [s24]; rw [Function.update_of_ne (by omega)]
      exact (hr_wv_regs 21 (by omega)).trans (by simp [s21])
    exact runs_store_iff.mpr ⟨g₀.arenaPtr + 1 + P_sub.verts.length, P_sub.edges.length,
      Expr.eval_reg_of_eq (by simp [s24]), Expr.eval_reg_of_eq h21', rfl, rfl, by simp [Expr.size]⟩
  have hr_regs : ∀ r ≤ 21, s25.regs r =
      if r = 18 then g₀.arenaPtr else if r = 19 then P_sub.verts.length
      else if r = 20 then g₀.hCur + 1 + P_sub.verts.length
      else if r = 21 then P_sub.edges.length else st.regs r := fun r hr => by
    dsimp only [s25, s24]
    rw [Function.update_of_ne (by omega), hr_wv_regs r hr]
    dsimp only [s21, s20, s19, s18]
    rcases (show r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ (r ≠ 18 ∧ r ≠ 19 ∧ r ≠ 20 ∧ r ≠ 21) by omega) with
      rfl | rfl | rfl | rfl | ⟨h18, h19, h20, h21⟩
    · simp [Function.update_of_ne]
    · simp [Function.update_of_ne]
    · simp [Function.update_of_ne]
    · simp
    · simp [Function.update_of_ne, h18, h19, h20, h21]
  have hm_vlen : s25.mem g₀.arenaPtr = (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.length := by
    dsimp only [s25, m2]
    rw [Function.update_of_ne (by omega), ha_wv_mem g₀.arenaPtr (by omega)]
    simp [m1, liftJSubWalk]
  have hm_verts : ∀ j < P_sub.verts.length, s25.mem (g₀.arenaPtr + 1 + j) =
      (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).verts.getD j 0 := fun j hj => by
    dsimp only [s25, m2]
    rw [Function.update_of_ne (by omega)]
    exact hv_wv_mem j hj
  have hm_elen : s25.mem (g₀.arenaPtr + 1 + P_sub.verts.length) =
      (liftJSubWalk (ctx.wd.comps[ci]'hci) P_sub).edges.length := by
    simp [s25, m2, liftJSubWalk]
  have hm_agr : ∀ a, ¬(g₀.arenaPtr ≤ a ∧ a ≤ g₀.arenaPtr + 1 + P_sub.verts.length) →
      s25.mem a = mem_gp a := fun a ha => by
    dsimp only [s25, m2]
    rw [Function.update_of_ne (by omega), ha_wv_mem a (by omega)]
    exact Function.update_of_ne (by omega) _ _
  obtain ⟨o, stF, c_cont, hr_cont, hQ⟩ :=
    hcont s25 c_wv hc_wv hr_regs (by simp [s25, s24]) hm_vlen hm_verts hm_elen hm_agr
  refine ⟨o, stF, c_wv, c_cont, _,
    runs_seq_iff.mpr (Or.inr ⟨s18, 5, _, hr18,
      runs_seq_iff.mpr (Or.inr ⟨s19, 3, _, hr19,
        runs_seq_iff.mpr (Or.inr ⟨s20, 6, _, hr20,
          runs_seq_iff.mpr (Or.inr ⟨s21, 3, _, hr21,
            runs_seq_iff.mpr (Or.inr ⟨sm1, 3, _, hm1_st,
              runs_seq_iff.mpr (Or.inr ⟨st_wv, c_wv, _, hr_wv,
                runs_seq_iff.mpr (Or.inr ⟨s24, 6, _, hr24,
                  runs_seq_iff.mpr (Or.inr ⟨s25, 3, c_cont, hm2_st, hr_cont, rfl⟩),
                  rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    hQ, by omega⟩

end MinCostFlow.Spanner
