module

public import MinCostFlow.Spanner.ProgTask2InitLoopBase

@[expose] public section

/-!
# Verified Initialization Phase of One Round of `task2Body`

Proves `t2Round_init_loop_ptriple`: executing the round header update and the DS initialization
loop (`forRange 20 (.const 0) (.reg 10)`) inside `task2Body` from a `T2LoopState` establishes
`T2StepInv`, `T2VcongRoundInv`, empty active/queue/deleted state, and the exact potential
`dsTotalPhi` within the amortized `K_init` budget.
-/

namespace MinCostFlow.Spanner

open WordRAM

lemma t2Round_init_loop_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (r_done : ℕ) (emb_prev emb : ℕ → Option Walk) (hCur0 arenaPtr del0 upd0 inn0 : ℕ)
    (hEta_succ : r_done + 1 ≤ eta1Bound ctx.wd inp.J) :
    let γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
    let gp0 := (ctx.wd.W.m - ctx.wd.j0Edges.length) - (unembeddedSetPure ctx.wd emb).card
    PTriple w p
      (fun st Φ => T2LoopState ctx stc r_done emb_prev emb hCur0 arenaPtr del0 upd0 inn0 st ∧ Φ = 0)
      (Stmt.assign 41 (t2Add (t2Ld (.reg 4) (.const 1)) (.const 1)) ;;
       t2St (.reg 4) (.const 1) (.reg 41) ;;
       t2St (.reg 4) (.const 28) (t2Mul (.reg 41) (.reg 40)) ;;
       t2St (.reg 4) (.const 2) (t2Add (t2Ld (.reg 4) (.const 2)) (.reg 10)) ;;
       forRange 20 (.const 0) (.reg 10) (t2InitBody dsBase))
      (pNormalPost fun st' Φ' => ∃ (g : T2Ghost impl.pathDS),
        T2StepInv ctx stc g st'.mem ∧
        T2VcongRoundInv ctx g ∧
        g.η₁ = r_done + 1 ∧ g.emb = emb ∧ g.emb_prev = emb ∧
        g.procVerts = ∅ ∧ g.drained = ∅ ∧ g.queue = [] ∧
        g.initCountJ = (r_done + 1) * ctx.wd.comps.length ∧
        g.initEdgesJ = (r_done + 1) * (ctx.wd.comps.map fun c => c.J_sub.m).sum ∧
        g.getPathCountJ = gp0 ∧ g.deleteCountJ = del0 ∧ g.prevDelCountJ = del0 ∧
        g.vcongUpdates = upd0 ∧ g.innerIters1 = inn0 ∧
        g.arenaPtr = arenaPtr ∧ g.queryId = ctx.wd.j0Edges.length + gp0 ∧
        hCur0 ≤ g.hCur ∧ (∀ ci, (g.states ci).Vhat = ∅ ∧ (g.states ci).deleted = ∅) ∧
        st'.regs 4 = inp.v1 ∧ st'.regs 10 = ctx.wd.comps.length ∧ st'.regs 12 = ctx.wd.W.m ∧
        st'.regs 18 = g.hCur ∧ st'.regs 31 = ctx.wInp.prep.aComps ∧
        st'.regs 32 = st'.mem (ctx.wInp.h + 12) ∧ st'.regs 33 = ctx.wInp.prep.phiNum_dec ∧
        st'.regs 34 = ctx.wInp.prep.phiDen_dec ∧ st'.regs 35 = ctx.wd.J0_strip.m ∧
        st'.regs 36 = inp.dsHandlesAddr ctx.wd.W.m ∧
        st'.regs 37 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 38 = inp.embWJAddr ∧
        st'.regs 39 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 40 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec ∧
        st'.regs 41 = r_done + 1 ∧
        Φ' = dsTotalPhi impl.pathDS (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length g.reps st'.mem)
      (fun _ => inp.J.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 52 * inp.J.m + 45) := by
  intro γJ gp0 st Φ ω ⟨hLS, hΦ0⟩
  subst hΦ0
  have db := drain_bounds ctx stc
  have hm := t2_maxWord_scalars ctx stc
  rcases hm with ⟨hv1_ds, _, _, hv1_w, _, _, _, hm_eta, htau_bd, hη_w⟩
  have hEtaCap : r_done + 1 ≤ Task2Input.eta1Cap impl inp.J :=
    le_trans hEta_succ (t2_eta1Bound_le_eta1Cap ctx)
  have hK_le : ctx.wd.comps.length ≤ inp.J.m := ctx.hK_le
  have hr1_w : r_done + 1 < 2 ^ w := lt_of_le_of_lt hEtaCap hη_w
  have hv1_1_w : inp.v1 + 1 < 2 ^ w := by omega
  have hv1_2_w : inp.v1 + 2 < 2 ^ w := by omega
  have hv1_28_w : inp.v1 + 28 < 2 ^ w := by omega
  have h28_val_w : (r_done + 1) * (ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
      ctx.wInp.prep.phiDen_dec) < 2 ^ w := by
    have h1 : (r_done + 1) * (ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
        ctx.wInp.prep.phiDen_dec) ≤ Task2Input.eta1Cap impl inp.J *
        ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hEtaCap)
    exact lt_of_le_of_lt h1 htau_bd
  have h2_val_w : (r_done + 1) * ctx.wd.comps.length < 2 ^ w := by
    by_cases hm0 : inp.J.m = 0
    · have hk0 : ctx.wd.comps.length = 0 := Nat.eq_zero_of_le_zero (hm0 ▸ hK_le)
      rw [hk0, Nat.mul_zero]; exact Nat.zero_lt_of_lt ctx.hww.1
    · have := Nat.mul_le_mul hEtaCap (le_trans hK_le (le_rfl))
      exact lt_of_le_of_lt this hm_eta
  have hslots := hLS.h_v1_slots
  let s41 : State := { mem := st.mem, regs := Function.update st.regs 41 (r_done + 1), pos := st.pos }
  have hr_s41 : Runs w p ω (Stmt.assign 41 (t2Add (t2Ld (.reg 4) (.const 1)) (.const 1))) st .normal s41 7 := by
    have he_a := Expr.eval_add (Expr.eval_reg_of_eq hLS.hr4) (Expr.eval_const (by omega : 1 < 2 ^ w)) hv1_1_w
    have he_ld := Expr.eval_load he_a
    rw [hslots.2.1] at he_ld
    have he_v := Expr.eval_add he_ld (Expr.eval_const (by omega : 1 < 2 ^ w)) hr1_w
    exact runs_assign_iff.mpr ⟨_, he_v, rfl, rfl, by simp [Expr.size]⟩
  let m1 := Function.update st.mem (inp.v1 + 1) (r_done + 1)
  let s1 : State := { mem := m1, regs := s41.regs, pos := st.pos }
  have hr_s1 : Runs w p ω (t2St (.reg 4) (.const 1) (.reg 41)) s41 .normal s1 5 := by
    have hr_4 : s41.regs 4 = inp.v1 := by simp (disch := decide) only [s41, Function.update_of_ne, hLS.hr4]
    have hr_41 : s41.regs 41 = r_done + 1 := by dsimp only [s41]; exact Function.update_self _ _ _
    have he_a := Expr.eval_add (Expr.eval_reg_of_eq hr_4) (Expr.eval_const (by omega : 1 < 2 ^ w)) hv1_1_w
    exact runs_store_iff.mpr ⟨_, _, he_a, Expr.eval_reg_of_eq hr_41, rfl, rfl, by simp [Expr.size]⟩
  let m28 := Function.update m1 (inp.v1 + 28)
    ((r_done + 1) * (ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec))
  let s28 : State := { mem := m28, regs := s41.regs, pos := st.pos }
  have hr_s28 : Runs w p ω (t2St (.reg 4) (.const 28) (t2Mul (.reg 41) (.reg 40))) s1 .normal s28 7 := by
    have hr_4 : s1.regs 4 = inp.v1 := by simp (disch := decide) only [s1, s41, Function.update_of_ne, hLS.hr4]
    have hr_41 : s1.regs 41 = r_done + 1 := by dsimp only [s1, s41]; exact Function.update_self _ _ _
    have hr_40 : s1.regs 40 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
        ctx.wInp.prep.phiDen_dec := by simp (disch := decide) only [s1, s41, Function.update_of_ne, hLS.hr40]
    have he_a := Expr.eval_add (Expr.eval_reg_of_eq hr_4) (Expr.eval_const (by omega : 28 < 2 ^ w)) hv1_28_w
    have he_v := Expr.eval_mul (Expr.eval_reg_of_eq hr_41) (Expr.eval_reg_of_eq hr_40) h28_val_w
    exact runs_store_iff.mpr ⟨_, _, he_a, he_v, rfl, rfl, by simp [Expr.size]⟩
  let m2 := Function.update m28 (inp.v1 + 2) ((r_done + 1) * ctx.wd.comps.length)
  let s2 : State := { mem := m2, regs := s41.regs, pos := st.pos }
  have hr_s2 : Runs w p ω (t2St (.reg 4) (.const 2) (t2Add (t2Ld (.reg 4) (.const 2)) (.reg 10))) s28 .normal s2 10 := by
    have hr_4 : s28.regs 4 = inp.v1 := by simp (disch := decide) only [s28, s41, Function.update_of_ne, hLS.hr4]
    have hr_10 : s28.regs 10 = ctx.wd.comps.length := by
      simp (disch := decide) only [s28, s41, Function.update_of_ne, hLS.hr10]
    have he_a := Expr.eval_add (Expr.eval_reg_of_eq hr_4) (Expr.eval_const (by omega : 2 < 2 ^ w)) hv1_2_w
    have he_ld := Expr.eval_load he_a
    change (t2Ld (.reg 4) (.const 2)).eval w s28 = some (m28 (inp.v1 + 2)) at he_ld
    have hm28_2 : m28 (inp.v1 + 2) = r_done * ctx.wd.comps.length := by
      simp [m28, m1, hslots.2.2.1]
    rw [hm28_2] at he_ld
    have hrw : r_done * ctx.wd.comps.length + ctx.wd.comps.length = (r_done + 1) * ctx.wd.comps.length := by ring
    have he_v := Expr.eval_add he_ld (Expr.eval_reg_of_eq hr_10) (hrw.symm ▸ h2_val_w)
    exact runs_store_iff.mpr ⟨_, _, he_a, hrw ▸ he_v, rfl, rfl, by simp [Expr.size]⟩
  have hm2_pre : ∀ x < inp.v1, m2 x = mem₀ x := fun x hx => by
    simp only [m2, m28, m1, Function.update_of_ne (by omega : x ≠ inp.v1 + 2),
      Function.update_of_ne (by omega : x ≠ inp.v1 + 28),
      Function.update_of_ne (by omega : x ≠ inp.v1 + 1)]
    exact hLS.agr_pre x hx
  have hK_w : (0 < ctx.wd.comps.length → ctx.wd.comps.length < 2 ^ w) := fun _ => by
    have : 1 ≤ Task2Input.eta1Cap impl inp.J := by unfold Task2Input.eta1Cap; exact Nat.le_add_right 1 _
    have := Nat.mul_le_mul this hK_le
    rw [Nat.one_mul] at this
    exact lt_of_le_of_lt this hm_eta
  obtain ⟨x_tau⟩ := pathDS_nonempty_tau impl.pathDS
  have hfor := PTriple.forRange_le (w := w) (p := p)
    (P := fun st_f Φ_f => st_f = s2 ∧ Φ_f = 0)
    (r := 20) (lo := .const 0) (hi := .reg 10) (body := t2InitBody dsBase)
    (Inv := T2InitLoopState ctx stc r_done m2 hCur0 del0 gp0)
    (stepCost := fun ci =>
      (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 42)
    0 ctx.wd.comps.length (Nat.zero_le _) ctx.hww.1 hK_w
    (fun st_f Φ_f ⟨hstf, hΦf⟩ => by
      subst hstf hΦf
      refine ⟨Expr.eval_const (by omega : 0 < 2 ^ w), ?_⟩
      refine ⟨hCur0, fun _ => { phiNum := 0, phiDen := 1, M := 0, G := ⟨0, []⟩, Vhat := ∅, deleted := ∅ },
        fun _ => x_tau,
        { hr4 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr4]
          hr10 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr10]
          hr12 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr12]
          hr20 := by dsimp only; exact Function.update_self _ _ _
          hr31 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr31]
          hr32 := by
            have hw20 := ctx.hv20
            have hr32_s : s2.regs 32 = st.mem (ctx.wInp.h + 12) := by
              simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr32]
            have hm2_12 : m2 (ctx.wInp.h + 12) = st.mem (ctx.wInp.h + 12) := by
              simp only [m2, m28, m1,
                Function.update_of_ne (by omega : ctx.wInp.h + 12 ≠ inp.v1 + 2),
                Function.update_of_ne (by omega : ctx.wInp.h + 12 ≠ inp.v1 + 28),
                Function.update_of_ne (by omega : ctx.wInp.h + 12 ≠ inp.v1 + 1)]
            simp only [Function.update_of_ne (by decide : (32 : ℕ) ≠ 20), hr32_s, hm2_12]
          hr33 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr33]
          hr34 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr34]
          hr35 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr35]
          hr36 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr36]
          hr37 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr37]
          hr38 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr38]
          hr39 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr39]
          hr40 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr40]
          hr41 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, Function.update_self]
          hr18 := by simp (disch := decide) only [s2, s41, Function.update_of_ne, hLS.hr18]
          hCur_lo := le_refl _
          hCur_le := hLS.hCur_le
          h3 := by
            have hne2 : inp.v1 + 3 ≠ inp.v1 + 2 := by omega
            have hne28 : inp.v1 + 3 ≠ inp.v1 + 28 := by omega
            have hne1 : inp.v1 + 3 ≠ inp.v1 + 1 := by omega
            simp only [s2, m2, m28, m1, Function.update_of_ne hne2, Function.update_of_ne hne28,
              Function.update_of_ne hne1, hslots.2.2.2.1, sumCompEdgesUpTo, List.take_zero,
              List.map_nil, List.sum_nil, Nat.add_zero]
          hframe := fun _ _ _ _ => rfl
          hDS :=
            { h_ge := hLS.hCur_lo
              zero_from := fun a ha => by
                have hds_a : stc.dsBaseAddr ≤ a := le_trans hLS.hCur_lo ha
                have : inp.v1 + 32 ≤ a := le_trans hv1_ds hds_a
                simp only [s2, m2, m28, m1,
                  Function.update_of_ne (by omega : a ≠ inp.v1 + 2),
                  Function.update_of_ne (by omega : a ≠ inp.v1 + 28),
                  Function.update_of_ne (by omega : a ≠ inp.v1 + 1),
                  hLS.hzf a ha]
              at_ci := fun _ h => absurd h (Nat.not_lt_zero _)
              disjoint := fun _ h => absurd h (Nat.not_lt_zero _) }
          hEmpty := fun _ h => absurd h (Nat.not_lt_zero _)
          hΦ := by simp [dsTotalPhi] }⟩)
    (fun _ _ _ _ _ hi => by rcases hi with ⟨_, _, _, hi⟩; exact hi.hr20)
    (fun _ _ _ _ _ hi => by rcases hi with ⟨_, _, _, hi⟩; exact Expr.eval_reg_of_eq hi.hr10)
    (fun i _ hi => by
      simpa only [List.getD_eq_getElem _ _ hi] using
        t2Init_loop_step ctx stc hSpec hEtaCap hLS.hDel_le (by have := hLS.hGet_le; omega)
          hm2_pre hi)
  obtain ⟨o_f, st_f, c_f, Φ_f, hr_f, hq_f, hc_f⟩ := hfor s2 0 ω ⟨rfl, rfl⟩
  cases o_f with
  | returned _ => exact absurd hq_f (by simp)
  | normal =>
    rcases hq_f with ⟨hCurF, statesF, repsF, hr4, hr10, hr12, _hr20, hr31, hr32, hr33, hr34, hr35, hr36, hr37, hr38, hr39, hr40,
      hr41, hr18, hCur_lo, hCur_le, h3_f, hframe_f, hDS_f, hEmpty_f, hΦ_f⟩
    let states' : ℕ → PathDSAbsState := fun ci =>
      if ci < ctx.wd.comps.length then statesF ci else
        { phiNum := 0, phiDen := 1, M := 0, G := ⟨0, []⟩, Vhat := ∅, deleted := ∅ }
    let embF := emb
    have hPreF : ∀ x < inp.v1, st_f.mem x = mem₀ x := fun x hx =>
      (hframe_f x (lt_of_lt_of_le hx (le_trans (Nat.le_add_right _ 32) hv1_ds)) (by omega)
        (fun k _ => by have := db.e_v1; have := db.e_emb; omega)).trans (hm2_pre x hx)
    have hStatF := (ctx.agrees_preserves_static hPreF).2.2.2.2.2.2.2
    have hMem_pre : ∀ a < stc.dsBaseAddr, a ≠ inp.v1 + 1 → a ≠ inp.v1 + 2 → a ≠ inp.v1 + 3 →
        a ≠ inp.v1 + 28 → (∀ ci < ctx.wd.comps.length, a ≠ inp.dsHandlesAddr ctx.wd.W.m + ci) →
        st_f.mem a = st.mem a := fun a ha h1 h2 h3 h28 hdl => by
      rw [hframe_f a ha h3 hdl]
      simp [m2, m28, m1, h1, h2, h28]
    have hslot_lt : ∀ k ≤ 31, k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 28 →
        st_f.mem (inp.v1 + k) = st.mem (inp.v1 + k) := fun k hk h1 h2 h3 h28 =>
      hMem_pre (inp.v1 + k) (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun ci _ => by have := db.e_v1; have := db.e_emb; omega)
    have h1_m : st_f.mem (inp.v1 + 1) = r_done + 1 := by
      rw [hframe_f (inp.v1 + 1) (by omega) (by omega) (fun ci _ => by have := db.e_v1; have := db.e_emb; omega)]
      simp [m2, m28, m1]
    have h2_m : st_f.mem (inp.v1 + 2) = (r_done + 1) * ctx.wd.comps.length := by
      rw [hframe_f (inp.v1 + 2) (by omega) (by omega) (fun ci _ => by have := db.e_v1; have := db.e_emb; omega)]
      simp [m2]
    have h28_m : st_f.mem (inp.v1 + 28) = (r_done + 1) *
        ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec := by
      rw [hframe_f (inp.v1 + 28) (by omega) (by omega) (fun ci _ => by have := db.e_v1; have := db.e_emb; omega)]
      simp [m2, m28, Nat.mul_assoc]
    have h3_m : st_f.mem (inp.v1 + 3) = (r_done + 1) * (ctx.wd.comps.map fun c => c.J_sub.m).sum := by
      rw [h3_f]
      have htk : sumCompEdgesUpTo ctx.wd.comps ctx.wd.comps.length =
          (ctx.wd.comps.map fun c => c.J_sub.m).sum := by simp [sumCompEdgesUpTo]
      rw [htk]; ring
    have hDS' : DSArrayAt impl.pathDS ctx.wd.comps ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
        ctx.wd.J0_strip.m w stc.dsBaseAddr (inp.dsHandlesAddr ctx.wd.W.m) hCurF st_f.mem
        ctx.wd.comps.length states' repsF :=
      { h_ge := hDS_f.h_ge
        zero_from := hDS_f.zero_from
        at_ci := fun ci hci => by simpa [states', hci] using hDS_f.at_ci ci hci
        disjoint := fun c1 h1 c2 h2 => hDS_f.disjoint c1 h1 c2 h2 }
    let g : T2Ghost impl.pathDS :=
      { η₁ := r_done + 1
        emb := emb
        emb_prev := emb
        states := states'
        reps := repsF
        drained := ∅
        procVerts := ∅
        queue := []
        initCountJ := (r_done + 1) * ctx.wd.comps.length
        initEdgesJ := (r_done + 1) * (ctx.wd.comps.map fun c => c.J_sub.m).sum
        getPathCountJ := gp0
        deleteCountJ := del0
        prevDelCountJ := del0
        vcongUpdates := upd0
        innerIters1 := inn0
        arenaPtr := arenaPtr
        queryId := ctx.wd.j0Edges.length + gp0
        hCur := hCurF }
    have hEmpty' : ∀ ci, (states' ci).Vhat = ∅ ∧ (states' ci).deleted = ∅ := fun ci => by
      by_cases hci : ci < ctx.wd.comps.length
      · simpa [states', hci] using hEmpty_f ci hci
      · simp [states', hci]
    have h_pre_eq : ∀ a < stc.nodesEnd, (∀ k < 32, a ≠ inp.v1 + k) →
        (∀ ci < ctx.wd.comps.length, a ≠ inp.dsHandlesAddr ctx.wd.W.m + ci) → st_f.mem a = st.mem a :=
      fun a ha hk hdl => hMem_pre a (lt_of_lt_of_le ha db.h_nds)
        (hk 1 (by decide)) (hk 2 (by decide)) (hk 3 (by decide)) (hk 28 (by decide)) hdl
    have h_vhead_nds : ∀ a, inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ≤ a → a < stc.nodesEnd →
        st_f.mem a = st.mem a := fun a ha1 ha2 =>
      h_pre_eq a ha2 (fun k hk => by have := db.e_v1; have := db.e_emb; have := db.e_hdl; omega)
        (fun ci hci => by have := db.e_hdl; omega)
    have hStepInv : T2StepInv ctx stc g st_f.mem :=
      { agr_pre := hPreF
        h0 := (hslot_lt 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.1
        h1 := h1_m
        hη_pos := by dsimp only [g]; omega
        hη_bd := hEta_succ
        h2 := h2_m
        hInitC := rfl
        h3 := h3_m
        hInitE := rfl
        h4 := (hslot_lt 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.1
        hGetC := by dsimp only [g, gp0]; have := hLS.hGet_le; omega
        h5 := (hslot_lt 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.1
        hDelEq := by simp [g, hEmpty']
        hPrevDel := by dsimp only [g]; simpa using hLS.hDel_le
        h6 := (hslot_lt 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.1
        hVcUpd := by dsimp only [g]; exact hLS.hVcU_le
        h7 := (hslot_lt 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.1
        hInner := by dsimp only [g]; simpa using hLS.hInn_le
        h8 := (hslot_lt 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.1
        h9 := (hslot_lt 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.1
        h10 := (hslot_lt 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.1
        h12 := (hslot_lt 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.1
        h13 := (hslot_lt 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.1
        h14 := (hslot_lt 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h15 := (hslot_lt 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h16 := (hslot_lt 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h17 := (hslot_lt 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h18 := (hslot_lt 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h19 := (hslot_lt 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h20 := (hslot_lt 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h21 := (hslot_lt 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h22 := (hslot_lt 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h23 := (hslot_lt 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h24 := (hslot_lt 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h25 := (hslot_lt 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h26 := (hslot_lt 26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hQid := rfl
        h27 := (hslot_lt 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h28 := h28_m
        h29 := (hslot_lt 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h30 := (hslot_lt 30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h31 := (hslot_lt 31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        hCeb := fun ci hci => by
          have ha_hi : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci < stc.nodesEnd := by
            have := db.e_ceb; have := db.e_vho; have := db.e_del
            have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps; have := db.e_ew
            have := db.e_q; have := db.h_nlo; omega
          rw [h_vhead_nds _ (by omega) ha_hi]
          exact hLS.hCeb ci hci
        hVho := fun ci hci => by
          have ha_hi : inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci < stc.nodesEnd := by
            have := db.e_vho; have := db.e_del
            have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps; have := db.e_ew
            have := db.e_q; have := db.h_nlo; omega
          rw [h_vhead_nds _ (by have := db.e_ceb; omega) ha_hi]
          exact hLS.hVho ci hci
        hInc := fun x hx => by
          have hi := hLS.hInc x hx
          have hvh_hi : inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x < stc.nodesEnd := by
            have := db.e_vhd; have := db.e_vc; have := db.e_ps; have := db.e_ew
            have := db.e_q; have := db.h_nlo; omega
          have hvh_eq : st_f.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) =
              st.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) :=
            h_vhead_nds _ (by have := db.e_ceb; have := db.e_vho; have := db.e_del; have := db.e_vh; omega) hvh_hi
          rw [hvh_eq]
          refine ⟨hi.1.mono fun a ha1 ha2 => h_vhead_nds a ?_ ha2, hi.2⟩
          have := db.e_ceb; have := db.e_vho; have := db.e_del; have := db.e_vh; have := db.e_vhd
          have := db.e_vc; have := db.e_ps; have := db.e_ew; have := db.e_q; omega
        hEmb := by
          intro eW heW
          have h_emb_eq : st_f.mem (inp.embWJAddr + eW) = st.mem (inp.embWJAddr + eW) :=
            hMem_pre _ (by have := db.e_emb; have := db.e_hdl; omega)
              (by have := db.e_v1; omega) (by have := db.e_v1; omega) (by have := db.e_v1; omega)
              (by have := db.e_v1; omega) (fun ci _ => by have := db.e_emb; omega)
          have h_ar_ds : arenaPtr ≤ stc.dsBaseAddr := by
            have := hLS.hGet_le
            have hj0 := (t2SetupHdr_word_bounds ctx).2.2.2.2.2.2.2.2.2.1
            have h1 := hLS.hAr_le
            have hsum : ctx.wd.j0Edges.length + (ctx.wd.W.m - ctx.wd.j0Edges.length - (unembeddedSetPure ctx.wd emb).card) ≤
                ctx.wd.W.m := by omega
            have hmul := Nat.mul_le_mul_right (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) hsum
            dsimp only [T2StaticData.dsBaseAddr]
            exact le_trans h1 (Nat.add_le_add_left hmul _)
          have hprev := hLS.hEmb eW heW
          dsimp only [EmbInv, g] at hprev ⊢
          cases he : emb eW with
          | none =>
            simp only [he] at hprev ⊢
            rwa [h_emb_eq]
          | some P =>
            simp only [he] at hprev ⊢
            rcases hprev with ⟨hlo, hhi, hwk⟩
            rw [h_emb_eq]
            refine ⟨hlo, hhi, fun i hi => ?_⟩
            have ha_lt : st.mem (inp.embWJAddr + eW) + i < arenaPtr := by omega
            have ha_ds : st.mem (inp.embWJAddr + eW) + i < stc.dsBaseAddr := lt_of_lt_of_le ha_lt h_ar_ds
            rw [hMem_pre _ ha_ds
              (by have := db.e_v1; have := db.e_emb; have := db.e_hdl; have := db.e_ceb; have := db.e_vho
                  have := db.e_del; have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
                  have := db.e_ew; have := db.e_q; have := db.h_nlo; omega)
              (by have := db.e_v1; have := db.e_emb; have := db.e_hdl; have := db.e_ceb; have := db.e_vho
                  have := db.e_del; have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
                  have := db.e_ew; have := db.e_q; have := db.h_nlo; omega)
              (by have := db.e_v1; have := db.e_emb; have := db.e_hdl; have := db.e_ceb; have := db.e_vho
                  have := db.e_del; have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
                  have := db.e_ew; have := db.e_q; have := db.h_nlo; omega)
              (by have := db.e_v1; have := db.e_emb; have := db.e_hdl; have := db.e_ceb; have := db.e_vho
                  have := db.e_del; have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
                  have := db.e_ew; have := db.e_q; have := db.h_nlo; omega)
              (fun ci _ => by
                have := db.e_hdl; have := db.e_ceb; have := db.e_vho; have := db.e_del; have := db.e_vh
                have := db.e_vhd; have := db.e_vc; have := db.e_ps; have := db.e_ew; have := db.e_q
                have := db.h_nlo; omega)]
            exact hwk i hi
        hAr_le := by dsimp only [g]; exact hLS.hAr_le
        hDS := hDS'
        hDelR := fun ci hci b hb => by
          have ha_lo : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ≤
              inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b := by
            have := db.e_ceb; have := db.e_vho; omega
          have ha_hi : inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b <
              stc.nodesEnd := by
            have h1 : compEdgeBase ctx.wd ci + b < compEdgeBase ctx.wd (ci + 1) := by
              have hb' : b < ctx.wd.comps[ci].J_sub.m := hb
              have heq := compEdgeBase_add_le hci
              omega
            have h2 : compEdgeBase ctx.wd ci + b < inp.J.m :=
              lt_of_lt_of_le h1 (le_trans (compEdgeBase_le_sum (wd := ctx.wd) (Nat.succ_le_of_lt hci)) db.h_jm)
            have ha3 := db.e_del.le; have ha4 := db.e_vh.le; have ha5 := db.e_vhd.le
            have ha6 := db.e_vc.le; have ha7 := db.e_ps.le; have ha8 := db.e_ew.le
            have ha9 := db.e_q.le; have ha10 := db.h_nlo; omega
          rw [h_vhead_nds _ ha_lo ha_hi]
          have hle := hLS.hDelR_le ci hci b hb
          simp only [g, hEmpty', Finset.notMem_empty, iff_false]
          exact ⟨by omega, by omega⟩
        hVhatS := fun ci hci y hy => by
          have ha_lo : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ≤
              inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y := by
            have := db.e_ceb; have := db.e_vho; have := db.e_del; omega
          have ha_hi : inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y <
              stc.nodesEnd := by
            have h1 : vhatBase ctx.wd ci + y < vhatBase ctx.wd (ci + 1) := by
              have hy' : y < ctx.wd.comps[ci].J_sub.n := hy
              have heq := vhatBase_add_le hci
              omega
            have h2 : vhatBase ctx.wd ci + y < 2 * inp.J.m :=
              lt_of_lt_of_le h1 (le_trans (vhatBase_le_sum (wd := ctx.wd) (Nat.succ_le_of_lt hci)) db.h_jn)
            have := db.e_vh.le; have := db.e_vhd.le; have := db.e_vc.le
            have := db.e_ps.le; have := db.e_ew.le; have := db.e_q.le; have := db.h_nlo; omega
          rw [h_vhead_nds _ ha_lo ha_hi]
          have hle := hLS.hVhatS_le ci hci y hy
          simp only [g, hEmpty', Finset.notMem_empty, iff_false]
          exact ⟨by omega, by omega⟩
        hDelSub := fun ci _ b hb => by simp [g, hEmpty'] at hb
        hVc := fun x hx => by
          have ha_lo : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ≤
              inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x := by
            have := db.e_ceb; have := db.e_vho; have := db.e_del
            have := db.e_vh; have := db.e_vhd; omega
          have ha_hi : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x < stc.nodesEnd := by
            have := db.e_vc; have := db.e_ps; have := db.e_ew
            have := db.e_q; have := db.h_nlo; omega
          rw [h_vhead_nds _ ha_lo ha_hi]
          exact hLS.hVc x hx
        hEwSt := fun x hx => by
          have ha_lo : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ≤
              inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x := by
            have := db.e_ceb; have := db.e_vho; have := db.e_del
            have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps; omega
          have ha_hi : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x < stc.nodesEnd := by
            have := db.e_ew; have := db.e_q; have := db.h_nlo; omega
          rw [h_vhead_nds _ ha_lo ha_hi]
          exact hLS.hEwSt x hx
        hProcS := fun x hx => by
          have ha_lo : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ≤
              inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x := by
            have := db.e_ceb; have := db.e_vho; have := db.e_del
            have := db.e_vh; have := db.e_vhd; have := db.e_vc; omega
          have ha_hi : inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x < stc.nodesEnd := by
            have := db.e_ps; have := db.e_ew; have := db.e_q; have := db.h_nlo; omega
          rw [h_vhead_nds _ ha_lo ha_hi]
          have hle := hLS.hProcS_le x hx
          simp only [g, Finset.notMem_empty, iff_false]; exact ⟨by omega, by omega⟩
        hProcSub := fun _ h => by simp [g] at h
        hQ_nd := by simp [g]
        hQ_sub := fun _ h => by simp [g] at h
        hDr_sub := by simp [g]
        hQ_mem := fun _ h => by simp [g] at h
        hQ_at := fun _ hi => by simp [g] at hi
        hDr_del := fun _ h => by simp [g] at h
        hPart := hLS.hPart
        hMono := fun _ _ => Or.inr rfl
        hj0 := hLS.hj0
        hELen := hLS.hELen
        hVc_prev := by simpa [g] using hLS.hVc_cur
        hVol_prev := by simpa [g] using hLS.hVol_cur
        hHCur_le := by
          dsimp only [g]
          have heq : (r_done + 1) * ctx.wd.comps.length + del0 + gp0 =
              r_done * ctx.wd.comps.length + ctx.wd.comps.length + del0 + gp0 := by ring
          rw [heq]; exact hCur_le }
    have hVcong : T2VcongRoundInv ctx g := by
      refine ⟨fun x hx => ?_, fun x hx _ => ?_⟩
      · have h1 := hLS.hVc_cur x hx
        have hτ : 0 ≤ ctx.wd.τ₁ := ctx.hw_okW.τ₁_nonneg
        dsimp only [g]; push_cast; linarith
      · have h1 := hLS.hVc_cur x hx
        have hτ : 0 ≤ ctx.wd.τ₁ := ctx.hw_okW.τ₁_nonneg
        dsimp only [g]; push_cast; linarith
    have hcost_hdr : (7 + (5 + (7 + (10 + c_f + 1) + 1) + 1) + 1) + Φ_f ≤
        inp.J.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 52 * inp.J.m + 45 := by
      have hrc : rangeCost (fun ci =>
          (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 42)
          0 ctx.wd.comps.length ≤
          inp.J.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 42 * inp.J.m := by
        rw [rangeCost_zero_eq_sum]
        have hsum_eq : (∑ ci ∈ Finset.range ctx.wd.comps.length,
            ((ctx.wd.comps.getD ci defaultCompInfo).J_sub.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 42)) =
            (∑ ci ∈ Finset.range ctx.wd.comps.length, (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m) *
              ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ + 42 * ctx.wd.comps.length := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm _ 42]
        have hsum_j : ∑ ci ∈ Finset.range ctx.wd.comps.length, (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m =
            (ctx.wd.comps.map fun c => c.J_sub.m).sum :=
          sum_range_getD_nat ctx.wd.comps defaultCompInfo (fun c => c.J_sub.m)
        have hjm_le : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m := by
          have h1 := ctx.hWInpJ ▸ mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
          change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m at h1
          omega
        rw [hsum_eq, hsum_j]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hjm_le) (Nat.mul_le_mul_left 42 hK_le)
      have hsz1 : (Expr.reg 10).size = 1 := rfl
      have hsz2 : (Expr.const 0).size = 1 := rfl
      rw [hsz1, hsz2] at hc_f
      simp only [Nat.sub_zero] at hc_f
      exact t2Round_init_cost_arith hK_le hrc hc_f
    have hrun := runs_seq_iff.mpr (Or.inr ⟨s41, 7, _, hr_s41,
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hr_s1,
        runs_seq_iff.mpr (Or.inr ⟨s28, 7, _, hr_s28,
          runs_seq_iff.mpr (Or.inr ⟨s2, 10, _, hr_s2, hr_f, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hsz : st_f.mem (ctx.wInp.h + 12) = m2 (ctx.wInp.h + 12) := by
      have hw20 := ctx.hv20
      rw [hframe_f _ (by omega) (by omega) (fun ci _ => by have := db.e_v1; have := db.e_emb; omega)]
    exact ⟨.normal, st_f, _, Φ_f, hrun, ⟨g, hStepInv, hVcong, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, hCur_lo, hEmpty', hr4, hr10, hr12, hr18, hr31,
      hr32.trans hsz.symm, hr33, hr34, hr35, hr36, hr37, hr38, hr39, hr40, hr41, hΦ_f⟩, hcost_hdr⟩

end MinCostFlow.Spanner
