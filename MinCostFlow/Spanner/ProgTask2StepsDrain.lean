module

public import MinCostFlow.Spanner.ProgTask2StepsDrainLoop

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Outer loop and full `PTriple` for `t2DrainQueue` -/

private lemma t2Drain_outer_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (g₀ : T2Ghost impl.pathDS) {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart) :
    let qTail := g₀.queue.length
    let drainedAt := fun k => g₀.drained ∪ (g₀.queue.take k).toFinset
    let kDel := t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      ctx.wd.J0_strip.m
    let undel := fun stFn : ℕ → PathDSAbsState => ∑ k ∈ Finset.range ctx.wd.comps.length,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.m -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.m).filter
          (· ∈ (stFn k).deleted)).card)
    let vh := fun stFn : ℕ → PathDSAbsState => ∑ k ∈ Finset.range ctx.wd.comps.length,
      ((ctx.wd.comps.getD k defaultCompInfo).J_sub.n -
        ((Finset.range (ctx.wd.comps.getD k defaultCompInfo).J_sub.n).filter
          (· ∈ (stFn k).Vhat)).card)
    let nodeRem := fun dr => ∑ y ∈ (Finset.range inp.H'.n).filter (· ∉ dr), (stc.L_inc y).length
    let Inv := fun (i : ℕ) (st : State) (Φ : ℕ) =>
      ∃ states reps hCur delCount,
        T2DrainInv ctx stc g₀ memStart (drainedAt i) states reps hCur delCount st.mem ∧
        st.regs 0 = inp.v1 ∧ st.regs 2 = qTail ∧ st.regs 3 = g₀.η₁ ∧
        st.regs 4 = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 5 = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 6 = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 7 = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 8 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 9 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 10 = inp.dsHandlesAddr ctx.wd.W.m ∧ st.regs 11 = hCur ∧
        st.regs 12 = i ∧
        Φ = t2RoundPhi impl.pathDS kDel 32 45 (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
          (undel states) (vh states) (nodeRem (drainedAt i)) reps st.mem
    PTriple w p (fun st Φ => ∃ st0, st = st0 ∧ Inv 0 { st0 with regs := Function.update st0.regs 12 0 } Φ)
      (forRange 12 (.const 0) (.reg 2) (
        Stmt.assign 13 (t2Ld (.reg 4) (.reg 12)) ;;
        Stmt.assign 14 (t2Ld (.reg 5) (.reg 13)) ;;
        Stmt.loop (.reg 14) (
          Stmt.assign 15 (.load (.reg 14)) ;;
          Stmt.assign 16 (t2Ld (.reg 14) (.const 1)) ;;
          Stmt.assign 17 (t2Add (t2Ld (.reg 6) (.reg 15)) (.reg 16)) ;;
          Stmt.cond (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)) (
            t2St (.reg 7) (.reg 17) (.reg 3) ;;
            t2St (.reg 0) (.const 5) (t2Add (t2Ld (.reg 0) (.const 5)) (.const 1)) ;;
            Stmt.assign 18 (t2Ld (.reg 10) (.reg 15)) ;;
            Stmt.assign 19 (.reg 11) ;;
            Stmt.call 11 (dsBase + 1) [.reg 18, .reg 16, .reg 11] ;;
            Stmt.assign 20 (.load (.reg 19)) ;;
            Stmt.assign 21 (t2Ld (.reg 8) (.reg 15)) ;;
            forRange 22 (.const 0) (.reg 20) (
              Stmt.assign 23 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 22))) ;;
              t2St (.reg 9) (t2Add (.reg 21) (.reg 23)) (.reg 3)
            )
          ) Stmt.nop ;;
          Stmt.assign 14 (t2Ld (.reg 14) (.const 2))
        )
      )) (pNormalPost (Inv qTail)) (fun _ => qTail * 25 + 7) := by
  intro qTail drainedAt kDel undel vh nodeRem Inv
  rcases drain_bounds ctx stc with ⟨h_v1, h_emb, h_hdl, h_ceb, h_vho, h_del, h_vh, h_vhd, h_vc, h_ps,
    h_ew, h_q, h_nlo, h_nds, h_dsc, h_stc, h_mhe, h_mwb, hW, _, _⟩
  have hq_le_nH : qTail ≤ inp.H'.n := by
    have hsub : g₀.queue.toFinset ⊆ Finset.range inp.H'.n := fun y hy =>
      Finset.mem_range.mpr (hS.hQ_sub y (List.mem_toFinset.mp hy)).1
    have hc := Finset.card_le_card hsub
    rwa [List.toFinset_card_of_nodup hS.hQ_nd, Finset.card_range] at hc
  have hq_w : qTail < 2 ^ w := by omega
  have hfor := PTriple.forRange_const (w := w) (p := p)
    (P := fun st Φ => ∃ st0, st = st0 ∧ Inv 0 { st0 with regs := Function.update st0.regs 12 0 } Φ)
    (r := 12) (lo := .const 0) (hi := .reg 2) (Inv := Inv) (stepBound := 14) (loVal := 0) (hiVal := qTail)
    (Nat.zero_le _) hW (fun _ => hq_w)
    (fun st Φ ⟨st0, hst, hI0⟩ => ⟨Expr.eval_const (by omega : 0 < 2 ^ w), by simpa [hst] using hI0⟩)
    (fun i st Φ _ _ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr12, _⟩ => hr12)
    (fun i st Φ _ _ ⟨_, _, _, _, _, _, hr2, _⟩ => Expr.eval_reg_of_eq hr2)
    fun i _ hi => by
      set x := g₀.queue[i]'hi
      have hx_lt : x < inp.H'.n := (hS.hQ_sub x (List.getElem_mem hi)).1
      have hq_w : inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + i < 2 ^ w := by omega
      have hv_w : inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x < 2 ^ w := by omega
      have hs1 : PTriple w p (Inv i) (Stmt.assign 13 (t2Ld (.reg 4) (.reg 12)))
          (pNormalPost fun st₁ Φ₁ => Inv i st₁ Φ₁ ∧ st₁.regs 13 = x) (fun _ => 5) := fun st Φ ω hI => by
        rcases hI with ⟨states, reps, hCur, delCount, hD, hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9,
          hr10, hr11, hr12, hΦ⟩
        have hm : st.mem (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + i) = x :=
          (hD.hAgr _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hS.hQ_at i hi)
        have hev : (t2Ld (.reg 4) (.reg 12)).eval w st = some x := by
          have he := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr4) (Expr.eval_reg_of_eq hr12) hq_w
          simpa [hm] using Expr.eval_load (w := w) he
        refine ⟨.normal, _, 5, Φ, runs_assign_iff.mpr ⟨x, hev, rfl, rfl, rfl⟩,
          ⟨⟨states, reps, hCur, delCount, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hΦ⟩,
            by dsimp only; exact Function.update_self _ _ _⟩, le_refl _⟩ <;>
          (dsimp only; rwa [Function.update_of_ne (by omega)])
      have hs2 : PTriple w p (fun st₁ Φ₁ => Inv i st₁ Φ₁ ∧ st₁.regs 13 = x)
          (Stmt.assign 14 (t2Ld (.reg 5) (.reg 13)))
          (pNormalPost fun st₂ Φ₂ =>
            ∃ states reps hCur delCount,
              T2DrainInv ctx stc g₀ memStart (drainedAt i) states reps hCur delCount st₂.mem ∧
              st₂.regs 0 = inp.v1 ∧ st₂.regs 2 = qTail ∧ st₂.regs 3 = g₀.η₁ ∧
              st₂.regs 4 = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length ∧
              st₂.regs 5 = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length ∧
              st₂.regs 6 = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ∧
              st₂.regs 7 = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ∧
              st₂.regs 8 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
              st₂.regs 9 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
              st₂.regs 10 = inp.dsHandlesAddr ctx.wd.W.m ∧ st₂.regs 11 = hCur ∧
              st₂.regs 12 = i ∧ st₂.regs 13 = x ∧
              st₂.regs 14 = st₂.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) ∧
              Φ₂ = t2RoundPhi impl.pathDS kDel 32 45 (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
                (undel states) (vh states) (nodeRem (drainedAt i)) reps st₂.mem)
          (fun _ => 5) := fun st₁ Φ ω ⟨⟨states, reps, hCur, delCount, hD, hr0, hr2, hr3, hr4, hr5,
            hr6, hr7, hr8, hr9, hr10, hr11, hr12, hΦ⟩, hr13⟩ => by
        have hev : (t2Ld (.reg 5) (.reg 13)).eval w st₁ =
            some (st₁.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) := by
          have he := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr5) (Expr.eval_reg_of_eq hr13) hv_w
          simpa using Expr.eval_load (w := w) he
        refine ⟨.normal, _, 5, Φ, runs_assign_iff.mpr ⟨_, hev, rfl, rfl, rfl⟩,
          ⟨states, reps, hCur, delCount, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            by dsimp only; exact Function.update_self _ _ _, hΦ⟩, le_refl _⟩ <;>
          (dsimp only; assumption)
      have hs3 := t2Drain_node_loop_ptriple ctx stc hSpec hS hi
      have hbody := hs1.seq_normal (T := fun _ => 14)
        (hs2.seq_normal (T := fun _ => 8) hs3 (fun _ _ _ _ => by omega)) (fun _ _ _ _ => by omega)
      refine PTriple.conseq hbody (fun _ _ h => h) (fun o st' Φ' h => ?_) (fun _ _ _ => by omega)
      cases o with
      | returned _ => exact False.elim h
      | normal =>
        rcases h with ⟨states', reps', hCur', delCount', hD', hr0, hr2, hr3, hr4, hr5, hr6, hr7,
          hr8, hr9, hr10, hr11, hr12, hΦ'⟩
        refine ⟨⟨states', reps', hCur', delCount', hD', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            by dsimp only; exact Function.update_self _ _ _, hΦ'⟩, hr12⟩ <;>
          (dsimp only; assumption)
  exact PTriple.conseq hfor (fun _ _ h => h) (fun _ _ _ h => h) fun _ _ _ => by
    simp only [Nat.sub_zero, Expr.size]; omega

/-- Complete amortized Word-RAM proof of `t2DrainQueueBody dsBase`. -/
lemma t2DrainQueue_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (g₀ : T2Ghost impl.pathDS) :
    PTriple w p
      (fun st Φ => st.regs 0 = inp.v1 ∧ st.regs 1 = g₀.hCur ∧
        T2StepInv ctx stc g₀ st.mem ∧ Φ = t2StepPhi ctx stc g₀ st.mem)
      (t2DrainQueueBody dsBase)
      (fun o st' Φ' => match o with
        | .normal => False
        | .returned v => ∃ g',
            v = g'.hCur ∧ g₀.hCur ≤ g'.hCur ∧ g'.η₁ = g₀.η₁ ∧ g'.emb = g₀.emb ∧
            g'.emb_prev = g₀.emb_prev ∧ g'.drained = g₀.procVerts ∧ g'.procVerts = g₀.procVerts ∧
            g'.queue = [] ∧ g'.initCountJ = g₀.initCountJ ∧ g'.initEdgesJ = g₀.initEdgesJ ∧
            g'.getPathCountJ = g₀.getPathCountJ ∧ g'.prevDelCountJ = g₀.prevDelCountJ ∧
            g'.vcongUpdates = g₀.vcongUpdates ∧ g'.innerIters1 = g₀.innerIters1 + g₀.queue.length ∧
            g'.arenaPtr = g₀.arenaPtr ∧ g'.queryId = g₀.queryId ∧
            (∀ ci, (g₀.states ci).deleted ⊆ (g'.states ci).deleted) ∧
            (∀ ci, (g₀.states ci).Vhat ⊆ (g'.states ci).Vhat) ∧
            T2StepInv ctx stc g' st'.mem ∧ Φ' = t2StepPhi ctx stc g' st'.mem)
      (fun _ => 25 * g₀.queue.length + 100) := by
  intro st Φ ω ⟨hr0, hr1, hS, hΦ⟩
  rcases drain_bounds ctx stc with ⟨h_v1, h_emb, h_hdl, h_ceb, h_vho, h_del, h_vh, h_vhd, h_vc, h_ps,
    h_ew, h_q, h_nlo, h_nds, h_dsc, h_stc, h_mhe, h_mwb, hW, _, _⟩
  have hinner_w : g₀.innerIters1 + g₀.queue.length < 2 ^ w := by
    have hsc := WitnessCoreInput.mkWitnessData_scalars ctx.wInp impl.constructExpander impl.pathDS.params ctx.WSubs ctx.hstat
    have hcaps := ctx.hWInpJ ▸ task2_scalars_le_caps ctx.hstat ctx.hφ_lb
    have hgp : g₀.getPathCountJ ≤ Task1Input.mwCap impl inp.J := by
      have : g₀.getPathCountJ ≤ ctx.wd.W.m := by have := hS.hGetC; omega
      exact le_trans this ctx.hmW_le
    have hγ : ctx.wd.γ_ExpPath ≤ (Task2Input.gammaExpCap impl inp.J : ℝ) := by
      rw [hsc.2.2.1]; exact_mod_cast hcaps.1
    have hr : ((g₀.innerIters1 + g₀.queue.length : ℕ) : ℝ) ≤
        ((Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J *
          (length inp.J inp.embJH + 1) : ℕ) : ℝ) := by
      push_cast
      have hgp_r : (g₀.getPathCountJ : ℝ) ≤ Task1Input.mwCap impl inp.J := by exact_mod_cast hgp
      have hlen_pos : 0 ≤ (length inp.J inp.embJH : ℝ) + 1 := by positivity
      have hγ_nonneg : (0 : ℝ) ≤ ctx.wd.γ_ExpPath :=
        le_trans (div_pos one_pos ctx.hw_okW.φ_ds_pos).le ctx.hw_okW.γ_ExpPath_ge
      calc ((g₀.innerIters1 : ℝ) + g₀.queue.length) ≤
            (g₀.getPathCountJ : ℝ) * (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1)) := hS.hInner
        _ ≤ (Task1Input.mwCap impl inp.J : ℝ) *
              ((Task2Input.gammaExpCap impl inp.J : ℝ) * ((length inp.J inp.embJH : ℝ) + 1)) :=
            mul_le_mul hgp_r (mul_le_mul_of_nonneg_right hγ hlen_pos) (mul_nonneg hγ_nonneg hlen_pos) (by positivity)
        _ = _ := by ring
    have hnat : g₀.innerIters1 + g₀.queue.length ≤
        Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J * (length inp.J inp.embJH + 1) := by
      exact_mod_cast hr
    have hmwb : Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J *
        (length inp.J inp.embJH + 1) ≤ Task2Input.maxWordBound impl inp := by
      unfold Task2Input.maxWordBound
      exact le_trans (by omega : Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J *
            (length inp.J inp.embJH + 1) ≤
          Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J *
            (length inp.J inp.embJH + 1) + inp.embVertSum + 4)
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    omega
  have hld0 : ∀ (s : State) (k : ℕ), s.regs 0 = inp.v1 → k ≤ 31 →
      (t2Ld (.reg 0) (.const k)).eval w s = some (s.mem (inp.v1 + k)) := fun s k hr hk => by
    simpa [t2Ld] using Expr.eval_load (w := w)
      (Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr) (Expr.eval_const (by omega : k < 2 ^ w)) (by omega))
  set s2 := { st with regs := Function.update st.regs 2 g₀.queue.length }
  have hr_2 : Runs w p ω (Stmt.assign 2 (t2Ld (.reg 0) (.const 27))) st .normal s2 5 :=
    runs_assign_iff.mpr ⟨g₀.queue.length, by simpa [hS.h27] using hld0 st 27 hr0 (by omega), rfl, rfl, by simp [Expr.size]⟩
  set s3 := { s2 with regs := Function.update s2.regs 3 g₀.η₁ }
  have hr_3 : Runs w p ω (Stmt.assign 3 (t2Ld (.reg 0) (.const 1))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨g₀.η₁, by
      have hm := hld0 s2 1 (by dsimp only [s2]; rw [Function.update_of_ne (by omega)]; exact hr0) (by omega)
      change (t2Ld (.reg 0) (.const 1)).eval w s2 = some (st.mem (inp.v1 + 1)) at hm
      rwa [hS.h1] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s4 := { s3 with regs := Function.update s3.regs 4 (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr_4 : Runs w p ω (Stmt.assign 4 (t2Ld (.reg 0) (.const 24))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨_, by
      have hm := hld0 s3 24 (by dsimp only [s3, s2]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr0) (by omega)
      change (t2Ld (.reg 0) (.const 24)).eval w s3 = some (st.mem (inp.v1 + 24)) at hm
      rwa [hS.h24] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s5 := { s4 with regs := Function.update s4.regs 5 (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr_5 : Runs w p ω (Stmt.assign 5 (t2Ld (.reg 0) (.const 20))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨_, by
      have hm := hld0 s4 20 (by dsimp only [s4, s3, s2]; simp [Function.update_of_ne, hr0]) (by omega)
      change (t2Ld (.reg 0) (.const 20)).eval w s4 = some (st.mem (inp.v1 + 20)) at hm
      rwa [hS.h20] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s6 := { s5 with regs := Function.update s5.regs 6 (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr_6 : Runs w p ω (Stmt.assign 6 (t2Ld (.reg 0) (.const 16))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨_, by
      have hm := hld0 s5 16 (by dsimp only [s5, s4, s3, s2]; simp [Function.update_of_ne, hr0]) (by omega)
      change (t2Ld (.reg 0) (.const 16)).eval w s5 = some (st.mem (inp.v1 + 16)) at hm
      rwa [hS.h16] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s7 := { s6 with regs := Function.update s6.regs 7 (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr_7 : Runs w p ω (Stmt.assign 7 (t2Ld (.reg 0) (.const 18))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨_, by
      have hm := hld0 s6 18 (by dsimp only [s6, s5, s4, s3, s2]; simp [Function.update_of_ne, hr0]) (by omega)
      change (t2Ld (.reg 0) (.const 18)).eval w s6 = some (st.mem (inp.v1 + 18)) at hm
      rwa [hS.h18] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s8 := { s7 with regs := Function.update s7.regs 8 (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr_8 : Runs w p ω (Stmt.assign 8 (t2Ld (.reg 0) (.const 17))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨_, by
      have hm := hld0 s7 17 (by dsimp only [s7, s6, s5, s4, s3, s2]; simp [Function.update_of_ne, hr0]) (by omega)
      change (t2Ld (.reg 0) (.const 17)).eval w s7 = some (st.mem (inp.v1 + 17)) at hm
      rwa [hS.h17] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s9 := { s8 with regs := Function.update s8.regs 9 (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length) }
  have hr_9 : Runs w p ω (Stmt.assign 9 (t2Ld (.reg 0) (.const 19))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨_, by
      have hm := hld0 s8 19 (by dsimp only [s8, s7, s6, s5, s4, s3, s2]; simp [Function.update_of_ne, hr0]) (by omega)
      change (t2Ld (.reg 0) (.const 19)).eval w s8 = some (st.mem (inp.v1 + 19)) at hm
      rwa [hS.h19] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s10 := { s9 with regs := Function.update s9.regs 10 (inp.dsHandlesAddr ctx.wd.W.m) }
  have hr_10 : Runs w p ω (Stmt.assign 10 (t2Ld (.reg 0) (.const 15))) s9 .normal s10 5 :=
    runs_assign_iff.mpr ⟨_, by
      have hm := hld0 s9 15 (by dsimp only [s9, s8, s7, s6, s5, s4, s3, s2]; simp [Function.update_of_ne, hr0]) (by omega)
      change (t2Ld (.reg 0) (.const 15)).eval w s9 = some (st.mem (inp.v1 + 15)) at hm
      rwa [hS.h15] at hm, rfl, rfl, by simp [Expr.size]⟩
  set s11 := { s10 with regs := Function.update s10.regs 11 g₀.hCur }
  have hr11_1 : s10.regs 1 = g₀.hCur := by
    dsimp only [s10, s9, s8, s7, s6, s5, s4, s3, s2]; simp [Function.update_of_ne, hr1]
  have hr_11 : Runs w p ω (Stmt.assign 11 (.reg 1)) s10 .normal s11 2 :=
    runs_assign_iff.mpr ⟨g₀.hCur, Expr.eval_reg_of_eq hr11_1, rfl, rfl, by simp [Expr.size]⟩
  set mem_p := Function.update st.mem (inp.v1 + 7) (g₀.innerIters1 + g₀.queue.length)
  set sP : State := { s11 with mem := mem_p }
  have hs11_0 : s11.regs 0 = inp.v1 := by
    dsimp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]; simp [Function.update_of_ne, hr0]
  have hs11_2 : s11.regs 2 = g₀.queue.length := by
    dsimp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]; simp [Function.update_of_ne]
  have hr_st7 : Runs w p ω (t2St (.reg 0) (.const 7) (t2Add (t2Ld (.reg 0) (.const 7)) (.reg 2))) s11 .normal sP 10 := by
    have he_a := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hs11_0) (Expr.eval_const (by omega : 7 < 2 ^ w)) (by omega)
    have he_ld := hld0 s11 7 hs11_0 (by omega)
    change (t2Ld (.reg 0) (.const 7)).eval w s11 = some (st.mem (inp.v1 + 7)) at he_ld
    rw [hS.h7] at he_ld
    have he_v := Expr.eval_add (w := w) he_ld (Expr.eval_reg_of_eq hs11_2) hinner_w
    exact runs_store_iff.mpr ⟨inp.v1 + 7, g₀.innerIters1 + g₀.queue.length, he_a, he_v, rfl, rfl, by simp [Expr.size]⟩
  have hPhi_p : t2StepPhi ctx stc g₀ mem_p = Φ := by
    rw [hΦ]
    have hp := (hS.hDS.frame_below (mem' := mem_p) hSpec.1
      (fun k hk => by dsimp only [mem_p]; exact Function.update_of_ne (by omega) _ _)
      (fun a ha => by dsimp only [mem_p]; exact Function.update_of_ne (by omega) _ _)).2
    simp only [t2StepPhi, t2RoundPhi]; rw [hp]
  have hD0 := t2DrainInv_init ctx stc g₀ hSpec.1 hS
  have hOuter := t2Drain_outer_ptriple ctx stc hSpec g₀ hS
  obtain ⟨o_out, st_out, c_out, Φ_out, hr_out, hq_out, hc_out⟩ :=
    hOuter sP Φ ω ⟨sP, rfl, g₀.states, g₀.reps, g₀.hCur, g₀.deleteCountJ,
      by simpa [List.take_zero, sP] using hD0,
      by dsimp only [sP]; rw [Function.update_of_ne (by omega)]; exact hs11_0,
      by dsimp only [sP]; rw [Function.update_of_ne (by omega)]; exact hs11_2,
      by dsimp only [sP, s11, s10, s9, s8, s7, s6, s5, s4, s3]; simp [Function.update_of_ne],
      by dsimp only [sP, s11, s10, s9, s8, s7, s6, s5, s4]; simp [Function.update_of_ne],
      by dsimp only [sP, s11, s10, s9, s8, s7, s6, s5]; simp [Function.update_of_ne],
      by dsimp only [sP, s11, s10, s9, s8, s7, s6]; simp [Function.update_of_ne],
      by dsimp only [sP, s11, s10, s9, s8, s7]; simp [Function.update_of_ne],
      by dsimp only [sP, s11, s10, s9, s8]; simp [Function.update_of_ne],
      by dsimp only [sP, s11, s10, s9]; simp [Function.update_of_ne],
      by dsimp only [sP, s11, s10]; simp [Function.update_of_ne],
      by dsimp only [sP, s11]; rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _,
      by dsimp only; exact Function.update_self _ _ _,
      by dsimp only [sP]; rw [← hPhi_p]; simp only [t2StepPhi, t2RoundPhi, t2UndelRem, t2VhatRem, t2NodeRem,
          t2KVhatStep, t2KNodeStep, List.take_zero, List.toFinset_nil, Finset.union_empty]⟩
  cases o_out with
  | returned _ => exact False.elim hq_out
  | normal =>
    rcases hq_out with ⟨states', reps', hCur', delCount', hDf, hr0', _, _, _, _, _, _, _, _, _, hr11', _, hΦf⟩
    have htake_all : g₀.queue.take g₀.queue.length = g₀.queue := List.take_length
    have hDr_eq : g₀.drained ∪ (g₀.queue.take g₀.queue.length).toFinset = g₀.procVerts := by
      ext y; simp only [htake_all, Finset.mem_union, List.mem_toFinset]
      exact ⟨fun h => h.elim (fun h => hS.hDr_sub h) (fun h => (hS.hQ_sub y h).2.1),
        fun hy => by_cases (fun h => Or.inl h) fun h => Or.inr ((hS.hQ_mem y hy).mpr h)⟩
    dsimp only at hDf hΦf
    rw [hDr_eq] at hDf hΦf
    have hD_fin := t2DrainInv_finish ctx stc g₀ hSpec.1 hS hDf
    set memF := Function.update st_out.mem (inp.v1 + 27) 0
    have hr_st27 : Runs w p ω (t2St (.reg 0) (.const 27) (.const 0)) st_out .normal { st_out with mem := memF } 5 :=
      runs_store_iff.mpr ⟨inp.v1 + 27, 0,
        Expr.eval_add (Expr.eval_reg_of_eq hr0') (Expr.eval_const (by omega : 27 < 2 ^ w)) (by omega),
        Expr.eval_const (by omega : 0 < 2 ^ w), rfl, rfl, by simp [Expr.size]⟩
    have hr_ret : Runs w p ω (Stmt.ret (.reg 11)) { st_out with mem := memF } (.returned hCur') { st_out with mem := memF } 2 :=
      runs_ret_iff.mpr ⟨hCur', Expr.eval_reg_of_eq hr11', rfl, rfl, by simp [Expr.size]⟩
    set g' : T2Ghost impl.pathDS :=
      { g₀ with
        states := states', reps := reps', drained := g₀.procVerts, queue := []
        deleteCountJ := delCount', innerIters1 := g₀.innerIters1 + g₀.queue.length, hCur := hCur' }
    have hPhi_fin : t2StepPhi ctx stc g' memF = Φ_out := by
      rw [hΦf]
      have hp := (hDf.hDS.frame_below (mem' := memF) hSpec.1
        (fun k hk => by dsimp only [memF]; exact Function.update_of_ne (by omega) _ _)
        (fun a ha => by dsimp only [memF]; exact Function.update_of_ne (by omega) _ _)).2
      simp only [t2StepPhi, t2RoundPhi, t2UndelRem, t2VhatRem, t2NodeRem, t2KVhatStep, t2KNodeStep, g']
      rw [hp]
    have hr_tail : Runs w p ω (t2St (.reg 0) (.const 27) (.const 0) ;; Stmt.ret (.reg 11)) st_out (.returned hCur')
        { st_out with mem := memF } 8 :=
      runs_seq_iff.mpr (Or.inr ⟨{ st_out with mem := memF }, 5, 2, hr_st27, hr_ret, rfl⟩)
    let d11 := 10 + (c_out + 8 + 1) + 1
    let d10 := 2 + d11 + 1
    let d9 := 5 + d10 + 1
    let d8 := 5 + d9 + 1
    let d7 := 5 + d8 + 1
    let d6 := 5 + d7 + 1
    let d5 := 5 + d6 + 1
    let d4 := 5 + d5 + 1
    let d3 := 5 + d4 + 1
    let d2 := 5 + d3 + 1
    have hr_body : Runs w p ω (t2DrainQueueBody dsBase) st (.returned hCur') { st_out with mem := memF }
        (67 + 1 + c_out + 1 + 8) :=
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, d2, hr_2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 5, d3, hr_3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 5, d4, hr_4,
            runs_seq_iff.mpr (Or.inr ⟨s5, 5, d5, hr_5,
              runs_seq_iff.mpr (Or.inr ⟨s6, 5, d6, hr_6,
                runs_seq_iff.mpr (Or.inr ⟨s7, 5, d7, hr_7,
                  runs_seq_iff.mpr (Or.inr ⟨s8, 5, d8, hr_8,
                    runs_seq_iff.mpr (Or.inr ⟨s9, 5, d9, hr_9,
                      runs_seq_iff.mpr (Or.inr ⟨s10, 5, d10, hr_10,
                        runs_seq_iff.mpr (Or.inr ⟨s11, 2, d11, hr_11,
                          runs_seq_iff.mpr (Or.inr ⟨sP, 10, c_out + 8 + 1, hr_st7,
                            runs_seq_iff.mpr (Or.inr ⟨st_out, c_out, 8, hr_out, hr_tail, rfl⟩),
                            rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
        by dsimp only [d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]; omega⟩)
    exact ⟨.returned hCur', { st_out with mem := memF }, 67 + 1 + c_out + 1 + 8, Φ_out, hr_body,
      ⟨g', rfl, hDf.hCur_ge, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        hDf.hDelMono, hDf.hVhMono, hD_fin, hPhi_fin.symm⟩, by dsimp only at ⊢ hc_out; omega⟩

end MinCostFlow.Spanner
