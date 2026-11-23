module

public import MinCostFlow.Spanner.ProgTask2InitLoopBase

@[expose] public section

/-!
# Verified Inner-Edge Step of Task 2 Round Loop 2

Defines the Task 2 Loop 2 statements (`t2InnerCiBody`, `t2OuterCiBody`, `t2RoundBody`), the round
potential `t2MidPhi` (extending `t2StepPhi` with per-unembedded-edge budget `t2EdgeBudget`), the
monotonic coverage predicate `t2Covered`, and proves `t2InnerStep_ptriple` (one `(ci, eL)` step
via `t2MiddleEdge_ptriple` or skipped when already embedded / covered by `Vhat`).
-/

namespace MinCostFlow.Spanner

open WordRAM

def t2InnerCiBody (selfBase : ℕ) : Stmt :=
  Stmt.assign 28 (t2Add (.reg 22) (.reg 27)) ;;
  Stmt.cond (t2Eq (t2Ld (.reg 38) (.reg 28)) (.const 0)) (
    Stmt.assign 29 (t2Ld (.reg 23) (t2Add (.const 2) (t2Mul (.const 2) (.reg 27)))) ;;
    Stmt.assign 30 (t2Ld (.reg 23) (t2Add (.const 3) (t2Mul (.const 2) (.reg 27)))) ;;
    Stmt.cond (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 29))) (.reg 41)) (
      Stmt.cond (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 30))) (.reg 41)) (
        Stmt.call 18 (selfBase + 3) [.reg 4, .reg 20, .reg 27, .reg 28, .reg 18]
      ) Stmt.nop
    ) Stmt.nop
  ) Stmt.nop

def t2OuterCiBody (selfBase : ℕ) : Stmt :=
  Stmt.assign 21 (t2Add (.reg 32) (t2Mul (.const 6) (.reg 20))) ;;
  Stmt.assign 22 (.load (.reg 21)) ;;
  Stmt.assign 23 (t2Ld (.reg 21) (.const 1)) ;;
  Stmt.assign 24 (t2Ld (.reg 21) (.const 5)) ;;
  Stmt.assign 25 (t2Ld (.reg 37) (.reg 20)) ;;
  forRange 27 (.const 0) (.reg 24) (t2InnerCiBody selfBase)

def t2RoundBody (selfBase dsBase : ℕ) : Stmt :=
  Stmt.assign 41 (t2Add (t2Ld (.reg 4) (.const 1)) (.const 1)) ;;
  t2St (.reg 4) (.const 1) (.reg 41) ;;
  t2St (.reg 4) (.const 28) (t2Mul (.reg 41) (.reg 40)) ;;
  t2St (.reg 4) (.const 2) (t2Add (t2Ld (.reg 4) (.const 2)) (.reg 10)) ;;
  forRange 20 (.const 0) (.reg 10) (t2InitBody dsBase) ;;
  forRange 20 (.const 0) (.reg 10) (t2OuterCiBody selfBase) ;;
  Stmt.assign 19 (t2Ld (.reg 4) (.const 30))

noncomputable def t2EdgeBudget (impl : SpannerToolImpl) (inp : Task2Input) : ℕ :=
  let γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
  ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ + 200 * γJ * (length inp.J inp.embJH + 1) + 600

noncomputable def t2MidPhi {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g : T2Ghost impl.pathDS)
    (mem : ℕ → ℕ) : ℕ :=
  t2StepPhi ctx stc g mem + (unembeddedSetPure ctx.wd g.emb).card * t2EdgeBudget impl inp

lemma t2StepPhi_empty_le {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g : T2Ghost impl.pathDS)
    (mem : ℕ → ℕ)
    (hDr : g.drained = ∅) :
    let γJq := impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
    t2StepPhi ctx stc g mem ≤
      dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length g.reps mem +
        inp.J.m * ⌈impl.pathDS.params.K_del * (γJq : ℝ)⌉₊ + 164 * inp.J.m + 45 * inp.embVertSum := by
  intro γJq
  have db := drain_bounds ctx stc
  have hds := t2_ds_bounds ctx.hWInpJ ctx.hstat ctx.hw_okW ctx.hφ_cap ctx.hφ_lb ctx.hww
  have hK_del : t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      ctx.wd.J0_strip.m ≤ ⌈impl.pathDS.params.K_del * (γJq : ℝ)⌉₊ + 100 := by
    unfold t2KDelPlusHdr
    exact Nat.add_le_add_right hds.2.1 100
  have hUndel : t2UndelRem ctx g ≤ inp.J.m := by
    unfold t2UndelRem
    have h1 : (∑ ci ∈ Finset.range ctx.wd.comps.length,
        ((ctx.wd.comps.getD ci defaultCompInfo).J_sub.m -
          ((Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m).filter
            (· ∈ (g.states ci).deleted)).card)) ≤
        ∑ ci ∈ Finset.range ctx.wd.comps.length, (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m :=
      Finset.sum_le_sum fun ci _ => Nat.sub_le _ _
    have h2 : ∑ ci ∈ Finset.range ctx.wd.comps.length,
        (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m =
        (ctx.wd.comps.map fun c => c.J_sub.m).sum :=
      sum_range_getD_nat ctx.wd.comps defaultCompInfo (fun c => c.J_sub.m)
    exact le_trans h1 (h2 ▸ db.h_jm)
  have hVhat : t2VhatRem ctx g ≤ 2 * inp.J.m := by
    unfold t2VhatRem
    have h1 : (∑ ci ∈ Finset.range ctx.wd.comps.length,
        ((ctx.wd.comps.getD ci defaultCompInfo).J_sub.n -
          ((Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n).filter
            (· ∈ (g.states ci).Vhat)).card)) ≤
        ∑ ci ∈ Finset.range ctx.wd.comps.length, (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n :=
      Finset.sum_le_sum fun ci _ => Nat.sub_le _ _
    have h2 : ∑ ci ∈ Finset.range ctx.wd.comps.length,
        (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n =
        (ctx.wd.comps.map fun c => c.J_sub.n).sum :=
      sum_range_getD_nat ctx.wd.comps defaultCompInfo (fun c => c.J_sub.n)
    exact le_trans h1 (h2 ▸ db.h_jn)
  have hNode : t2NodeRem ctx stc g ≤ inp.embVertSum := by
    unfold t2NodeRem
    rw [hDr]
    have h1 : (Finset.range inp.H'.n).filter (· ∉ (∅ : Finset ℕ)) = Finset.range inp.H'.n := by
      ext x; simp
    rw [h1]
    exact stc.hL_sum
  have hm1 : t2UndelRem ctx g * t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec
      ctx.wInp.prep.phiDen_dec ctx.wd.J0_strip.m ≤
      inp.J.m * ⌈impl.pathDS.params.K_del * (γJq : ℝ)⌉₊ + 100 * inp.J.m := by
    have := Nat.mul_le_mul hUndel hK_del
    rw [Nat.mul_add, Nat.mul_comm inp.J.m 100] at this
    exact this
  have hm2 : t2VhatRem ctx g * t2KVhatStep ≤ 64 * inp.J.m := by
    unfold t2KVhatStep; omega
  have hm3 : t2NodeRem ctx stc g * t2KNodeStep ≤ 45 * inp.embVertSum := by
    unfold t2KNodeStep; omega
  unfold t2StepPhi t2RoundPhi
  omega

def t2Covered {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (g : T2Ghost impl.pathDS) (ci eL : ℕ) : Prop :=
  let c := ctx.wd.comps.getD ci defaultCompInfo
  let eLoc := c.W_sub.edges.getD eL (0, 0)
  (g.emb (c.wStart + eL)).isSome = true ∨ eLoc.1 ∈ (g.states ci).Vhat ∨ eLoc.2 ∈ (g.states ci).Vhat

lemma t2Covered_mono_emb_vhat {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T2Ctx impl inp mem₀ w} {g g' : T2Ghost impl.pathDS} {ci eL eW : ℕ} {P : Walk}
    (hemb : g'.emb = Function.update g.emb eW (some P))
    (hvhat : ∀ k, (g.states k).Vhat ⊆ (g'.states k).Vhat)
    (hc : t2Covered ctx g ci eL) :
    t2Covered ctx g' ci eL := by
  rcases hc with h1 | h2 | h3
  · left
    rw [hemb]
    by_cases he : (ctx.wd.comps.getD ci defaultCompInfo).wStart + eL = eW
    · rw [he, Function.update_self]; rfl
    · rw [Function.update_of_ne he]; exact h1
  · right; left; exact hvhat ci h2
  · right; right; exact hvhat ci h3

lemma t2StaticOut_compExt {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T2Ctx impl inp mem₀ w} {mem : ℕ → ℕ} (hSt : ctx.StaticOutAt mem) :
    let aCompExt := mem (ctx.wInp.h + 12)
    let wAddr := mem (ctx.wInp.h + 13)
    let wWNumAddr := mem (ctx.wInp.h + 14)
    ctx.wInp.h + 20 ≤ aCompExt ∧
      aCompExt + 6 * ctx.wd.comps.length ≤ wAddr ∧
      wWNumAddr = wAddr + (2 + 2 * ctx.wd.W.m) ∧
      wWNumAddr + ctx.wd.W.m ≤ inp.v1 ∧
      CompExtAt mem aCompExt ctx.wInp.prep.phiNum_dec wAddr ctx.wd.comps := by
  rcases hSt with ⟨_, _, _, _, _, _, _, _, _, _, _, hw20, ha_wAddr, hwNum_eq, hwNum_v1, hCompExt, _⟩
  exact ⟨hw20, ha_wAddr, hwNum_eq, hwNum_v1, hCompExt⟩

structure T2InnerInvData {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (r_done : ℕ)
    (emb₀ : ℕ → Option Walk) (ci wSubPtr : ℕ) (eL : ℕ)
    (g : T2Ghost impl.pathDS) (st : State) (Φ : ℕ) : Prop where
  hr4 : st.regs 4 = inp.v1
  hr10 : st.regs 10 = ctx.wd.comps.length
  hr12 : st.regs 12 = ctx.wd.W.m
  hr20 : st.regs 20 = ci
  hr22 : st.regs 22 = ctx.wd.comps[ci]?.elim 0 CompInfo.wStart
  hr23 : st.regs 23 = wSubPtr
  hr24 : st.regs 24 = ctx.wd.comps[ci]?.elim 0 (fun c => c.W_sub.m)
  hr25 : st.regs 25 = vhatBase ctx.wd ci
  hr27 : st.regs 27 = eL
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
  hwSub_g : ∀ (hci : ci < ctx.wd.comps.length),
    st.mem (st.mem (ctx.wInp.h + 12) + 6 * ci + 1) = wSubPtr ∧
    GraphAt st.mem wSubPtr ctx.wd.comps[ci].W_sub ∧
    wSubPtr + (2 + 2 * ctx.wd.comps[ci].W_sub.m) ≤ st.mem (ctx.wInp.h + 13)
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
  hcov_cur : ∀ eL' < eL, t2Covered ctx g ci eL'
  hPhi : Φ = t2MidPhi ctx stc g st.mem

def T2InnerInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (r_done : ℕ)
    (emb₀ : ℕ → Option Walk) (ci wSubPtr : ℕ) (eL : ℕ) (st : State) (Φ : ℕ) : Prop :=
  ∃ g : T2Ghost impl.pathDS, T2InnerInvData ctx stc r_done emb₀ ci wSubPtr eL g st Φ

private lemma t2Inner_edge_cost_arith {c_m Φ_step Φ_step' card' B_base : ℕ}
    (hm : c_m + Φ_step' ≤ B_base + 500 + Φ_step) :
    (4 + (6 + (9 + (9 + (8 + (8 + (5 + c_m + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
      (Φ_step' + card' * (B_base + 600)) ≤
    60 + (Φ_step + (card' + 1) * (B_base + 600)) := by
  nlinarith

lemma t2InnerStep_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hp_mid : p.procs[selfBase + 3]? = some (t2MiddleEdgeBody dsBase (selfBase + 4)))
    (hp_drain : p.procs[selfBase + 4]? = some (t2DrainQueueBody dsBase))
    {r_done ci wSubPtr eL : ℕ} {emb₀ : ℕ → Option Walk}
    (hci : ci < ctx.wd.comps.length) (heL : eL < ctx.wd.comps[ci].W_sub.m) :
    PTriple w p
      (T2InnerInv ctx stc r_done emb₀ ci wSubPtr eL)
      (t2InnerCiBody selfBase)
      (pNormalPost fun st₁ Φ₁ =>
        T2InnerInv ctx stc r_done emb₀ ci wSubPtr (eL + 1)
          { st₁ with regs := Function.update st₁.regs 27 (eL + 1) } Φ₁ ∧ st₁.regs 27 = eL)
      (fun _ => 60) := by
  intro st Φ ω ⟨g, hI⟩
  have db := drain_bounds ctx stc
  have hm := t2_maxWord_scalars ctx stc
  rcases hm with ⟨hv1_ds, _, _, hv1_w, _, _, _, hm_eta, _, hη_w⟩
  have hS := hI.hStep
  have hstat := (ctx.agrees_preserves_static hS.agr_pre).2.2.2.2.2.2.2
  rcases t2StaticOut_compExt hstat with ⟨hw20, ha_wAddr, hwNum_eq, hwNum_v1, hCompExt⟩
  rcases hI.hwSub_g hci with ⟨hwSub_ptr, hwSub_g, hwSub_le⟩
  have hcp := ctx.hw_okW.comp_props ci hci
  have hm_edge := mkW_W_edges_comp ctx.hws hci heL
  set c := ctx.wd.comps[ci]
  set eW := c.wStart + eL
  have hc_getD : ctx.wd.comps.getD ci defaultCompInfo = c := List.getD_eq_getElem _ _ hci
  have hr22_eq : st.regs 22 = c.wStart := by
    rw [hI.hr22, List.getElem?_eq_getElem hci]; rfl
  have hr24_eq : st.regs 24 = c.W_sub.m := by
    rw [hI.hr24, List.getElem?_eq_getElem hci]; rfl
  have heW_m : eW < ctx.wd.W.m := hm_edge.1
  have hw_gt1 : 1 < 2 ^ w := ctx.hww.1
  have hm_w : ctx.wd.W.m < 2 ^ w := by
    have : ctx.wd.W.m ≤ inp.v1 := by omega
    omega
  have heW_w : eW < 2 ^ w := lt_of_lt_of_le heW_m hm_w.le
  have hemb_w : inp.embWJAddr + eW < 2 ^ w := by
    have : inp.embWJAddr + eW < inp.dsHandlesAddr ctx.wd.W.m := by rw [← db.e_emb]; omega
    have hds_w : stc.dsBaseAddr < 2 ^ w :=
      lt_of_le_of_lt (le_trans db.h_dsc (le_trans db.h_stc db.h_mhe)) db.h_mwb
    omega
  have hr28 : Runs w p ω (Stmt.assign 28 (t2Add (.reg 22) (.reg 27))) st .normal
      { st with regs := Function.update st.regs 28 eW } 4 := by
    have he := Expr.eval_add (Expr.eval_reg_of_eq hr22_eq) (Expr.eval_reg_of_eq hI.hr27) heW_w
    exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, by simp [Expr.size]⟩
  let s28 : State := { st with regs := Function.update st.regs 28 eW }
  have hemb_s28_38 : s28.regs 38 = inp.embWJAddr := by
    simp (disch := decide) only [s28, Function.update_of_ne, hI.hr38]
  have hemb_s28_28 : s28.regs 28 = eW := by
    dsimp only [s28]; exact Function.update_self _ _ _
  have he_emb_ptr : (t2Ld (.reg 38) (.reg 28)).eval w s28 = some (st.mem (inp.embWJAddr + eW)) :=
    Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hemb_s28_38) (Expr.eval_reg_of_eq hemb_s28_28) hemb_w)
  by_cases hnone : g.emb eW = none
  · have hm_emb0 : st.mem (inp.embWJAddr + eW) = 0 := by
      have h := hS.hEmb eW heW_m
      simpa [EmbInv, hnone] using h
    have he_eq : (t2Eq (t2Ld (.reg 38) (.reg 28)) (.const 0)).eval w s28 = some 1 :=
      Expr.eval_eq_true he_emb_ptr (Expr.eval_const (by omega : 0 < 2 ^ w)) hm_emb0 hw_gt1
    have heL_lt_w : 2 + 2 * eL < 2 ^ w := by
      have : wSubPtr + (2 + 2 * c.W_sub.m) ≤ inp.v1 := by omega
      omega
    have h2eL_w : 2 * eL < 2 ^ w := by omega
    have h3eL_w : 3 + 2 * eL < 2 ^ w := by omega
    have hu_ptr_w : wSubPtr + (2 + 2 * eL) < 2 ^ w := by omega
    have hv_ptr_w : wSubPtr + (3 + 2 * eL) < 2 ^ w := by omega
    set u_loc := c.W_sub.edges[eL].1
    set v_loc := c.W_sub.edges[eL].2
    have hu_mem : st.mem (wSubPtr + (2 + 2 * eL)) = u_loc := by
      rw [← Nat.add_assoc]; exact graphAt_edge_fst hwSub_g heL
    have hv_mem : st.mem (wSubPtr + (3 + 2 * eL)) = v_loc := by
      rw [← Nat.add_assoc]; exact graphAt_edge_snd hwSub_g heL
    have hu_lt : u_loc < c.J_sub.n := by
      have hv := hcp.2.2.2.2.2.2.2.2.2.2.2.2.1 c.W_sub.edges[eL] (List.getElem_mem _)
      omega
    have hv_lt : v_loc < c.J_sub.n := by
      have hv := hcp.2.2.2.2.2.2.2.2.2.2.2.2.1 c.W_sub.edges[eL] (List.getElem_mem _)
      omega
    have huv_w : (∀ k < 4, k < 2 ^ w) := fun k hk => by
      have : 4 ≤ 2 ^ w := by have := db.e_v1; have := hw_gt1; omega
      omega
    have hds_w : stc.dsBaseAddr < 2 ^ w :=
      lt_of_le_of_lt (le_trans db.h_dsc (le_trans db.h_stc db.h_mhe)) db.h_mwb
    have hvbase_u : vhatBase ctx.wd ci + u_loc < 2 ^ w := by
      have h1 : vhatBase ctx.wd ci + u_loc < vhatBase ctx.wd (ci + 1) := by
        have := vhatBase_add_le hci; dsimp only [c] at hu_lt; omega
      have h2 : vhatBase ctx.wd ci + u_loc < 2 * inp.J.m :=
        lt_of_lt_of_le h1 (le_trans (vhatBase_le_sum (Nat.succ_le_of_lt hci)) db.h_jn)
      have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
      have := db.e_ew; have := db.e_q; have := db.h_nlo; have := db.h_nds; omega
    have hvbase_v : vhatBase ctx.wd ci + v_loc < 2 ^ w := by
      have h1 : vhatBase ctx.wd ci + v_loc < vhatBase ctx.wd (ci + 1) := by
        have := vhatBase_add_le hci; dsimp only [c] at hv_lt; omega
      have h2 : vhatBase ctx.wd ci + v_loc < 2 * inp.J.m :=
        lt_of_lt_of_le h1 (le_trans (vhatBase_le_sum (Nat.succ_le_of_lt hci)) db.h_jn)
      have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
      have := db.e_ew; have := db.e_q; have := db.h_nlo; have := db.h_nds; omega
    have hvst_u : inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + (vhatBase ctx.wd ci + u_loc) < 2 ^ w := by
      have h1 : vhatBase ctx.wd ci + u_loc < vhatBase ctx.wd (ci + 1) := by
        have := vhatBase_add_le hci; dsimp only [c] at hu_lt; omega
      have h2 : vhatBase ctx.wd ci + u_loc < 2 * inp.J.m :=
        lt_of_lt_of_le h1 (le_trans (vhatBase_le_sum (Nat.succ_le_of_lt hci)) db.h_jn)
      have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
      have := db.e_ew; have := db.e_q; have := db.h_nlo; have := db.h_nds; omega
    have hvst_v : inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + (vhatBase ctx.wd ci + v_loc) < 2 ^ w := by
      have h1 : vhatBase ctx.wd ci + v_loc < vhatBase ctx.wd (ci + 1) := by
        have := vhatBase_add_le hci; dsimp only [c] at hv_lt; omega
      have h2 : vhatBase ctx.wd ci + v_loc < 2 * inp.J.m :=
        lt_of_lt_of_le h1 (le_trans (vhatBase_le_sum (Nat.succ_le_of_lt hci)) db.h_jn)
      have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
      have := db.e_ew; have := db.e_q; have := db.h_nlo; have := db.h_nds; omega
    let s29 : State := { s28 with regs := Function.update s28.regs 29 u_loc }
    have hr29 : Runs w p ω (Stmt.assign 29 (t2Ld (.reg 23) (t2Add (.const 2) (t2Mul (.const 2) (.reg 27)))))
        s28 .normal s29 9 := by
      have h23 : s28.regs 23 = wSubPtr := by simp (disch := decide) only [s28, Function.update_of_ne, hI.hr23]
      have h27 : s28.regs 27 = eL := by simp (disch := decide) only [s28, Function.update_of_ne, hI.hr27]
      have he := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h23)
        (Expr.eval_add (Expr.eval_const (huv_w 2 (by decide)))
          (Expr.eval_mul (Expr.eval_const (huv_w 2 (by decide))) (Expr.eval_reg_of_eq h27) h2eL_w) heL_lt_w)
        hu_ptr_w)
      rw [hu_mem] at he
      exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
    let s30 : State := { s29 with regs := Function.update s29.regs 30 v_loc }
    have hr30 : Runs w p ω (Stmt.assign 30 (t2Ld (.reg 23) (t2Add (.const 3) (t2Mul (.const 2) (.reg 27)))))
        s29 .normal s30 9 := by
      have h23 : s29.regs 23 = wSubPtr := by simp (disch := decide) only [s29, s28, Function.update_of_ne, hI.hr23]
      have h27 : s29.regs 27 = eL := by simp (disch := decide) only [s29, s28, Function.update_of_ne, hI.hr27]
      have he := Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h23)
        (Expr.eval_add (Expr.eval_const (huv_w 3 (by decide)))
          (Expr.eval_mul (Expr.eval_const (huv_w 2 (by decide))) (Expr.eval_reg_of_eq h27) h2eL_w) h3eL_w)
        hv_ptr_w)
      rw [hv_mem] at he
      exact runs_assign_iff.mpr ⟨_, he, rfl, rfl, rfl⟩
    have hvhs_u := hS.hVhatS ci hci u_loc hu_lt
    have hvhs_v := hS.hVhatS ci hci v_loc hv_lt
    have hs30_39 : s30.regs 39 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length := by
      simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr39]
    have hs30_25 : s30.regs 25 = vhatBase ctx.wd ci := by
      simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr25]
    have hs30_29 : s30.regs 29 = u_loc := by
      simp (disch := decide) only [s30, Function.update_of_ne, s29, Function.update_self]
    have hs30_30 : s30.regs 30 = v_loc := by
      dsimp only [s30]; exact Function.update_self _ _ _
    have hs30_41 : s30.regs 41 = r_done + 1 := by
      simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr41]
    have he_u_stamp : (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 29))).eval w s30 =
        some (st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + u_loc)) := by
      rw [Nat.add_assoc]
      exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hs30_39)
        (Expr.eval_add (Expr.eval_reg_of_eq hs30_25) (Expr.eval_reg_of_eq hs30_29) hvbase_u) hvst_u)
    have he_v_stamp : (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 30))).eval w s30 =
        some (st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + v_loc)) := by
      rw [Nat.add_assoc]
      exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hs30_39)
        (Expr.eval_add (Expr.eval_reg_of_eq hs30_25) (Expr.eval_reg_of_eq hs30_30) hvbase_v) hvst_v)
    by_cases hu_in : u_loc ∈ (g.states ci).Vhat
    · have hu_st_eq : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + u_loc) =
          r_done + 1 := by
        rw [← hI.hη]; exact hvhs_u.2.mpr hu_in
      have he_lt_u : (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 29))) (.reg 41)).eval w s30 = some 0 :=
        Expr.eval_lt_false he_u_stamp (Expr.eval_reg_of_eq hs30_41)
          (by rw [hu_st_eq]) hw_gt1
      have hr_tot : Runs w p ω (t2InnerCiBody selfBase) st .normal s30
          (4 + (6 + (9 + (9 + (8 + 1 + 1) + 1) + 1) + 1) + 1) := by
        dsimp only [t2InnerCiBody]
        refine runs_seq_iff.mpr (Or.inr ⟨s28, 4, (6 + (9 + (9 + (8 + 1 + 1) + 1) + 1) + 1), hr28,
          runs_cond_iff.mpr ⟨1, (9 + (9 + (8 + 1 + 1) + 1) + 1), he_eq, ?_, rfl⟩, rfl⟩)
        simp only [Nat.one_ne_zero, ↓reduceIte]
        refine runs_seq_iff.mpr (Or.inr ⟨s29, 9, (9 + (8 + 1 + 1) + 1), hr29,
          runs_seq_iff.mpr (Or.inr ⟨s30, 9, (8 + 1 + 1), hr30,
            runs_cond_iff.mpr ⟨0, 1, he_lt_u, ?_, rfl⟩, rfl⟩), rfl⟩)
        simp only [↓reduceIte]
        exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
      have hcov_next : ∀ eL' < eL + 1, t2Covered ctx g ci eL' := fun eL' heL' => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp heL' with hlt | heq
        · exact hI.hcov_cur eL' hlt
        · rw [heq]; right; left
          have huv_getD : c.W_sub.edges.getD eL (0, 0) = (u_loc, v_loc) := List.getD_eq_getElem _ _ heL
          simpa only [t2Covered, hc_getD, huv_getD] using hu_in
      let stOut := { s30 with regs := Function.update s30.regs 27 (eL + 1) }
      have hInvNext : T2InnerInvData ctx stc r_done emb₀ ci wSubPtr (eL + 1) g stOut Φ :=
        { hr4 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr4]
          hr10 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr10]
          hr12 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr12]
          hr20 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr20]
          hr22 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr22]
          hr23 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr23]
          hr24 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr24]
          hr25 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr25]
          hr27 := by dsimp only [stOut]; exact Function.update_self _ _ _
          hr31 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr31]
          hr32 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr32]
          hr33 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr33]
          hr34 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr34]
          hr35 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr35]
          hr36 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr36]
          hr37 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr37]
          hr38 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr38]
          hr39 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr39]
          hr40 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr40]
          hr41 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr41]
          hwSub_g := hI.hwSub_g
          hr18 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr18]
          hStep := hI.hStep
          hVcong := hI.hVcong
          hη := hI.hη
          hemb_prev := hI.hemb_prev
          hq := hI.hq
          hDr := hI.hDr
          hInitC := hI.hInitC
          hInitE := hI.hInitE
          har := hI.har
          hcov_prev := hI.hcov_prev
          hcov_cur := hcov_next
          hPhi := hI.hPhi }
      exact ⟨.normal, s30, _, Φ, hr_tot,
        ⟨⟨g, hInvNext⟩, by simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr27]⟩,
        by dsimp only; omega⟩
    · have hu_lt_eta : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + u_loc) <
          r_done + 1 := by
        have hle : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + u_loc) ≤
            r_done + 1 := hI.hη ▸ hvhs_u.1
        have hne : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + u_loc) ≠
            r_done + 1 := fun heq => hu_in (hvhs_u.2.mp (hI.hη ▸ heq))
        omega
      have he_lt_u : (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 29))) (.reg 41)).eval w s30 = some 1 :=
        Expr.eval_lt_true he_u_stamp (Expr.eval_reg_of_eq hs30_41) hu_lt_eta hw_gt1
      by_cases hv_in : v_loc ∈ (g.states ci).Vhat
      · have hv_st_eq : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + v_loc) =
            r_done + 1 := by
          rw [← hI.hη]; exact hvhs_v.2.mpr hv_in
        have he_lt_v : (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 30))) (.reg 41)).eval w s30 = some 0 :=
          Expr.eval_lt_false he_v_stamp (Expr.eval_reg_of_eq hs30_41) (by rw [hv_st_eq]) hw_gt1
        have hr_tot : Runs w p ω (t2InnerCiBody selfBase) st .normal s30
            (4 + (6 + (9 + (9 + (8 + (8 + 1 + 1) + 1) + 1) + 1) + 1) + 1) := by
          dsimp only [t2InnerCiBody]
          refine runs_seq_iff.mpr (Or.inr ⟨s28, 4, (6 + (9 + (9 + (8 + (8 + 1 + 1) + 1) + 1) + 1) + 1), hr28,
            runs_cond_iff.mpr ⟨1, (9 + (9 + (8 + (8 + 1 + 1) + 1) + 1) + 1), he_eq, ?_, rfl⟩, rfl⟩)
          simp only [Nat.one_ne_zero, ↓reduceIte]
          refine runs_seq_iff.mpr (Or.inr ⟨s29, 9, (9 + (8 + (8 + 1 + 1) + 1) + 1), hr29,
            runs_seq_iff.mpr (Or.inr ⟨s30, 9, (8 + (8 + 1 + 1) + 1), hr30,
              runs_cond_iff.mpr ⟨1, (8 + 1 + 1), he_lt_u, ?_, rfl⟩, rfl⟩), rfl⟩)
          simp only [Nat.one_ne_zero, ↓reduceIte]
          refine runs_cond_iff.mpr ⟨0, 1, he_lt_v, ?_, rfl⟩
          simp only [↓reduceIte]
          exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
        have hcov_next : ∀ eL' < eL + 1, t2Covered ctx g ci eL' := fun eL' heL' => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp heL' with hlt | heq
          · exact hI.hcov_cur eL' hlt
          · rw [heq]; right; right
            have huv_getD : c.W_sub.edges.getD eL (0, 0) = (u_loc, v_loc) := List.getD_eq_getElem _ _ heL
            simpa only [t2Covered, hc_getD, huv_getD] using hv_in
        let stOut := { s30 with regs := Function.update s30.regs 27 (eL + 1) }
        have hInvNext : T2InnerInvData ctx stc r_done emb₀ ci wSubPtr (eL + 1) g stOut Φ :=
          { hr4 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr4]
            hr10 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr10]
            hr12 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr12]
            hr20 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr20]
            hr22 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr22]
            hr23 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr23]
            hr24 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr24]
            hr25 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr25]
            hr27 := by dsimp only [stOut]; exact Function.update_self _ _ _
            hr31 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr31]
            hr32 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr32]
            hr33 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr33]
            hr34 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr34]
            hr35 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr35]
            hr36 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr36]
            hr37 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr37]
            hr38 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr38]
            hr39 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr39]
            hr40 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr40]
            hr41 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr41]
            hwSub_g := hI.hwSub_g
            hr18 := by simp (disch := decide) only [stOut, s30, s29, s28, Function.update_of_ne, hI.hr18]
            hStep := hI.hStep
            hVcong := hI.hVcong
            hη := hI.hη
            hemb_prev := hI.hemb_prev
            hq := hI.hq
            hDr := hI.hDr
            hInitC := hI.hInitC
            hInitE := hI.hInitE
            har := hI.har
            hcov_prev := hI.hcov_prev
            hcov_cur := hcov_next
            hPhi := hI.hPhi }
        exact ⟨.normal, s30, _, Φ, hr_tot,
          ⟨⟨g, hInvNext⟩, by simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr27]⟩,
          by dsimp only; omega⟩
      · have hv_lt_eta : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + v_loc) <
            r_done + 1 := by
          have hle : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + v_loc) ≤
              r_done + 1 := hI.hη ▸ hvhs_v.1
          have hne : st.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + v_loc) ≠
              r_done + 1 := fun heq => hv_in (hvhs_v.2.mp (hI.hη ▸ heq))
          omega
        have he_lt_v : (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 30))) (.reg 41)).eval w s30 = some 1 :=
          Expr.eval_lt_true he_v_stamp (Expr.eval_reg_of_eq hs30_41) hv_lt_eta hw_gt1
        have hu_not : (ctx.wd.comps[ci].W_sub.edges.getD eL (0, 0)).1 ∉ (g.states ci).Vhat := by
          rwa [List.getD_eq_getElem _ _ heL]
        have hv_not : (ctx.wd.comps[ci].W_sub.edges.getD eL (0, 0)).2 ∉ (g.states ci).Vhat := by
          rwa [List.getD_eq_getElem _ _ heL]
        have hmid_pt := t2MiddleEdge_ptriple ctx stc hSpec hp_drain g hI.hVcong hI.hq hI.har
          hci heL rfl hnone hu_not hv_not
        let callArgs : List ℕ := [inp.v1, ci, eL, eW, g.hCur]
        let stCall := startState callArgs st.mem st.pos
        have hCallPre : stCall.regs 0 = inp.v1 ∧ stCall.regs 1 = ci ∧ stCall.regs 2 = eL ∧
            stCall.regs 3 = eW ∧ stCall.regs 4 = g.hCur ∧
            T2StepInv ctx stc g stCall.mem ∧
            t2StepPhi ctx stc g st.mem = t2StepPhi ctx stc g stCall.mem :=
          ⟨rfl, rfl, rfl, rfl, rfl, hS, rfl⟩
        obtain ⟨o_m, st_m, c_m, Φ_m, hrun_m, hq_m, hcost_m⟩ :=
          hmid_pt stCall (t2StepPhi ctx stc g st.mem) ω hCallPre
        cases o_m with
        | normal => exact absurd hq_m (by simp)
        | returned hCur' =>
          rcases hq_m with ⟨g', rfl, _, hg'_η, ⟨P_sub, _, _, _, _, hg'_emb⟩,
            hg'_prev, hg'_dr, hg'_q, hg'_ic, hg'_ie, _, _, _, hg'_ar_stc, _, _, hg'_vhat,
            hStep', hVcong', rfl⟩
          let s18 : State := { mem := st_m.mem, regs := Function.update s30.regs 18 g'.hCur, pos := st_m.pos }
          have hs30_4 : s30.regs 4 = inp.v1 := by
            simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr4]
          have hs30_20 : s30.regs 20 = ci := by
            simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr20]
          have hs30_27 : s30.regs 27 = eL := by
            simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr27]
          have hs30_28 : s30.regs 28 = eW := by
            simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, Function.update_self]
          have hs30_18 : s30.regs 18 = g.hCur := by
            simp (disch := decide) only [s30, s29, s28, Function.update_of_ne, hI.hr18]
          have he_call : Runs w p ω (Stmt.call 18 (selfBase + 3) [.reg 4, .reg 20, .reg 27, .reg 28, .reg 18])
              s30 .normal s18 (5 + c_m + 1) := by
            refine runs_call_iff.mpr ⟨callArgs, t2MiddleEdgeBody dsBase (selfBase + 4), .returned g'.hCur,
              st_m, c_m, ?_, hp_mid, hrun_m, rfl, rfl, by simp [argsSize, Expr.size]⟩
            simp [callArgs, evalArgs, Expr.eval_reg_of_eq hs30_4, Expr.eval_reg_of_eq hs30_20,
              Expr.eval_reg_of_eq hs30_27, Expr.eval_reg_of_eq hs30_28, Expr.eval_reg_of_eq hs30_18]
          have hr_tot : Runs w p ω (t2InnerCiBody selfBase) st .normal s18
              (4 + (6 + (9 + (9 + (8 + (8 + (5 + c_m + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
            dsimp only [t2InnerCiBody]
            refine runs_seq_iff.mpr (Or.inr ⟨s28, 4, _, hr28,
              runs_cond_iff.mpr ⟨1, (9 + (9 + (8 + (8 + (5 + c_m + 1) + 1) + 1) + 1) + 1), he_eq, ?_, rfl⟩, rfl⟩)
            simp only [Nat.one_ne_zero, ↓reduceIte]
            refine runs_seq_iff.mpr (Or.inr ⟨s29, 9, (9 + (8 + (8 + (5 + c_m + 1) + 1) + 1) + 1), hr29,
              runs_seq_iff.mpr (Or.inr ⟨s30, 9, (8 + (8 + (5 + c_m + 1) + 1) + 1), hr30,
                runs_cond_iff.mpr ⟨1, (8 + (5 + c_m + 1) + 1), he_lt_u, ?_, rfl⟩, rfl⟩), rfl⟩)
            simp only [Nat.one_ne_zero, ↓reduceIte]
            refine runs_cond_iff.mpr ⟨1, (5 + c_m + 1), he_lt_v, ?_, rfl⟩
            simp only [Nat.one_ne_zero, ↓reduceIte]
            exact he_call
          have hcard_drop : (unembeddedSetPure ctx.wd g'.emb).card + 1 = (unembeddedSetPure ctx.wd g.emb).card := by
            rw [hg'_emb]
            exact (t2_unembedded_erase_card (wd := ctx.wd) heW_m hnone).2.2
          have hwSub_g' : ∀ (hci' : ci < ctx.wd.comps.length),
              st_m.mem (st_m.mem (ctx.wInp.h + 12) + 6 * ci + 1) = wSubPtr ∧
              GraphAt st_m.mem wSubPtr ctx.wd.comps[ci].W_sub ∧
              wSubPtr + (2 + 2 * ctx.wd.comps[ci].W_sub.m) ≤ st_m.mem (ctx.wInp.h + 13) := fun hci' => by
            have h12_eq : st_m.mem (ctx.wInp.h + 12) = st.mem (ctx.wInp.h + 12) := by
              have := ctx.hv20; rw [hStep'.agr_pre _ (by omega), hS.agr_pre _ (by omega)]
            have h13_eq : st_m.mem (ctx.wInp.h + 13) = st.mem (ctx.wInp.h + 13) := by
              have := ctx.hv20; rw [hStep'.agr_pre _ (by omega), hS.agr_pre _ (by omega)]
            have ha_lt_v1 : st.mem (ctx.wInp.h + 12) + 6 * ci + 1 < inp.v1 := by omega
            have hptr_eq : st_m.mem (st_m.mem (ctx.wInp.h + 12) + 6 * ci + 1) = wSubPtr := by
              rw [h12_eq, hStep'.agr_pre _ ha_lt_v1, ← hS.agr_pre _ ha_lt_v1]
              exact hwSub_ptr
            have hG' : GraphAt st_m.mem wSubPtr ctx.wd.comps[ci].W_sub := fun j hj => by
              have hj_v1 : wSubPtr + j < inp.v1 :=
                lt_of_lt_of_le (Nat.add_lt_add_left (by rw [← graph_encode_length _]; exact hj) wSubPtr)
                  (le_trans hwSub_le (by have := hwNum_eq; have := hwNum_v1; omega))
              rw [hStep'.agr_pre _ hj_v1, ← hS.agr_pre _ hj_v1]; exact hwSub_g j hj
            exact ⟨hptr_eq, hG', by rw [h13_eq]; exact hwSub_le⟩
          have h32_eq : s18.regs 32 = st_m.mem (ctx.wInp.h + 12) := by
            have := ctx.hv20
            have hreg : s18.regs 32 = st.mem (ctx.wInp.h + 12) := by
              simp (disch := decide) only [s18, s30, s29, s28, Function.update_of_ne, hI.hr32]
            rw [hreg, hStep'.agr_pre _ (by omega), hS.agr_pre _ (by omega)]
          have hcov_prev' : ∀ ci' < ci, ∀ eL' < (ctx.wd.comps.getD ci' defaultCompInfo).W_sub.m,
              t2Covered ctx g' ci' eL' := fun ci' hci' eL' heL' =>
            t2Covered_mono_emb_vhat hg'_emb hg'_vhat (hI.hcov_prev ci' hci' eL' heL')
          have hcov_cur' : ∀ eL' < eL + 1, t2Covered ctx g' ci eL' := fun eL' heL' => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp heL' with hlt | rfl
            · exact t2Covered_mono_emb_vhat hg'_emb hg'_vhat (hI.hcov_cur eL' hlt)
            · left; rw [hc_getD, hg'_emb, Function.update_self]; rfl
          let stOut := { s18 with regs := Function.update s18.regs 27 (eL + 1) }
          have hInvNext : T2InnerInvData ctx stc r_done emb₀ ci wSubPtr (eL + 1) g' stOut
              (t2MidPhi ctx stc g' st_m.mem) :=
            { hr4 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr4]
              hr10 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr10]
              hr12 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr12]
              hr20 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr20]
              hr22 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr22]
              hr23 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr23]
              hr24 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr24]
              hr25 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr25]
              hr27 := by dsimp only [stOut]; exact Function.update_self _ _ _
              hr31 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr31]
              hr32 := by
                have : stOut.regs 32 = s18.regs 32 := by
                  simp (disch := decide) only [stOut, Function.update_of_ne]
                exact this.trans h32_eq
              hr33 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr33]
              hr34 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr34]
              hr35 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr35]
              hr36 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr36]
              hr37 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr37]
              hr38 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr38]
              hr39 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr39]
              hr40 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr40]
              hr41 := by simp (disch := decide) only [stOut, s18, s30, s29, s28, Function.update_of_ne, hI.hr41]
              hwSub_g := hwSub_g'
              hr18 := by simp (disch := decide) only [stOut, s18, Function.update_of_ne, Function.update_self]
              hStep := hStep'
              hVcong := hVcong'
              hη := hg'_η.trans hI.hη
              hemb_prev := hg'_prev.trans hI.hemb_prev
              hq := hg'_q
              hDr := hg'_dr
              hInitC := hg'_ic.trans hI.hInitC
              hInitE := hg'_ie.trans hI.hInitE
              har := hg'_ar_stc
              hcov_prev := hcov_prev'
              hcov_cur := hcov_cur'
              hPhi := rfl }
          have hcost_tot : (4 + (6 + (9 + (9 + (8 + (8 + (5 + c_m + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
              t2MidPhi ctx stc g' st_m.mem ≤ 60 + Φ := by
            rw [hI.hPhi]
            unfold t2MidPhi t2EdgeBudget
            rw [← hcard_drop]
            rw [show ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ +
                200 * impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m * (length inp.J inp.embJH + 1) + 600 =
              (⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ +
                200 * impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m * (length inp.J inp.embJH + 1)) + 600 from rfl]
            exact t2Inner_edge_cost_arith (by
              dsimp only at hcost_m
              have h1 : 200 * impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m *
                  (length inp.J inp.embJH + 1) +
                  ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ +
                  500 =
                  (⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ +
                  200 * impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m * (length inp.J inp.embJH + 1)) +
                  500 := by ring
              rwa [← h1])
          exact ⟨.normal, s18, _, t2MidPhi ctx stc g' st_m.mem, hr_tot,
            ⟨⟨g', hInvNext⟩, by simp (disch := decide) only [s18, s30, s29, s28, Function.update_of_ne, hI.hr27]⟩,
            hcost_tot⟩
  · have hm_emb_ne : st.mem (inp.embWJAddr + eW) ≠ 0 := by
      have h := hS.hEmb eW heW_m
      cases he : g.emb eW with
      | none => exact absurd he hnone
      | some P =>
        rw [he] at h
        dsimp only [EmbInv] at h
        have h1 := stc.hNodes_lo
        have : inp.v1 + 32 ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length := by
          have := db.e_v1; have := db.e_emb; have := db.e_hdl; have := db.e_ceb; have := db.e_vho
          have := db.e_del; have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
          have := db.e_ew; have := db.e_q; omega
        omega
    have he_eq : (t2Eq (t2Ld (.reg 38) (.reg 28)) (.const 0)).eval w s28 = some 0 :=
      Expr.eval_eq_false he_emb_ptr (Expr.eval_const (by omega : 0 < 2 ^ w)) hm_emb_ne hw_gt1
    have hr_tot : Runs w p ω (t2InnerCiBody selfBase) st .normal s28 (4 + (6 + 1 + 1) + 1) := by
      dsimp only [t2InnerCiBody]
      have hr_nop : Runs w p ω Stmt.nop s28 .normal s28 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
      have hcd1 : Runs w p ω
          (Stmt.cond (t2Eq (t2Ld (.reg 38) (.reg 28)) (.const 0))
            (Stmt.assign 29 (t2Ld (.reg 23) (t2Add (.const 2) (t2Mul (.const 2) (.reg 27)))) ;;
             Stmt.assign 30 (t2Ld (.reg 23) (t2Add (.const 3) (t2Mul (.const 2) (.reg 27)))) ;;
             Stmt.cond (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 29))) (.reg 41)) (
               Stmt.cond (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 30))) (.reg 41)) (
                 Stmt.call 18 (selfBase + 3) [.reg 4, .reg 20, .reg 27, .reg 28, .reg 18]
               ) Stmt.nop
             ) Stmt.nop)
            Stmt.nop)
          s28 .normal s28 (6 + 1 + 1) :=
        runs_cond_iff.mpr ⟨0, 1, he_eq, by simpa using hr_nop, rfl⟩
      exact runs_seq_iff.mpr (Or.inr ⟨s28, 4, _, hr28, hcd1, rfl⟩)
    have hcov_next : ∀ eL' < eL + 1, t2Covered ctx g ci eL' := fun eL' heL' => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp heL' with hlt | rfl
      · exact hI.hcov_cur eL' hlt
      · left; rw [hc_getD]
        cases he : g.emb eW with
        | none => exact absurd he hnone
        | some _ => rfl
    let stOut := { s28 with regs := Function.update s28.regs 27 (eL + 1) }
    have hInvNext : T2InnerInvData ctx stc r_done emb₀ ci wSubPtr (eL + 1) g stOut Φ :=
      { hr4 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr4]
        hr10 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr10]
        hr12 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr12]
        hr20 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr20]
        hr22 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr22]
        hr23 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr23]
        hr24 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr24]
        hr25 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr25]
        hr27 := by dsimp only [stOut]; exact Function.update_self _ _ _
        hr31 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr31]
        hr32 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr32]
        hr33 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr33]
        hr34 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr34]
        hr35 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr35]
        hr36 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr36]
        hr37 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr37]
        hr38 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr38]
        hr39 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr39]
        hr40 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr40]
        hr41 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr41]
        hwSub_g := hI.hwSub_g
        hr18 := by simp (disch := decide) only [stOut, s28, Function.update_of_ne, hI.hr18]
        hStep := hI.hStep
        hVcong := hI.hVcong
        hη := hI.hη
        hemb_prev := hI.hemb_prev
        hq := hI.hq
        hDr := hI.hDr
        hInitC := hI.hInitC
        hInitE := hI.hInitE
        har := hI.har
        hcov_prev := hI.hcov_prev
        hcov_cur := hcov_next
        hPhi := hI.hPhi }
    exact ⟨.normal, s28, _, Φ, hr_tot,
      ⟨⟨g, hInvNext⟩, by simp (disch := decide) only [s28, Function.update_of_ne, hI.hr27]⟩,
      by dsimp only; omega⟩

end MinCostFlow.Spanner
