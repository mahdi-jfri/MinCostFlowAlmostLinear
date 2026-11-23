module

public import MinCostFlow.Spanner.ProgTask2StepsDrainTrue

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Inner node-drain loop `PTriple` for `t2DrainQueue` -/

lemma t2Drain_node_loop_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    {g₀ : T2Ghost impl.pathDS} {memStart : ℕ → ℕ} (hS : T2StepInv ctx stc g₀ memStart)
    {i : ℕ} (hi : i < g₀.queue.length) :
    let x := g₀.queue[i]'hi
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
    let Pre := fun (st : State) (Φ : ℕ) =>
      ∃ states reps hCur delCount,
        T2DrainInv ctx stc g₀ memStart (drainedAt i) states reps hCur delCount st.mem ∧
        st.regs 0 = inp.v1 ∧ st.regs 2 = g₀.queue.length ∧ st.regs 3 = g₀.η₁ ∧
        st.regs 4 = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 5 = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 6 = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 7 = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 8 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 9 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st.regs 10 = inp.dsHandlesAddr ctx.wd.W.m ∧ st.regs 11 = hCur ∧
        st.regs 12 = i ∧ st.regs 13 = x ∧ st.regs 14 = st.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) ∧
        Φ = t2RoundPhi impl.pathDS kDel 32 45 (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
          (undel states) (vh states) (nodeRem (drainedAt i)) reps st.mem
    let Post := fun (st' : State) (Φ' : ℕ) =>
      ∃ states' reps' hCur' delCount',
        T2DrainInv ctx stc g₀ memStart (drainedAt (i + 1)) states' reps' hCur' delCount' st'.mem ∧
        st'.regs 0 = inp.v1 ∧ st'.regs 2 = g₀.queue.length ∧ st'.regs 3 = g₀.η₁ ∧
        st'.regs 4 = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 5 = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 6 = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 7 = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 8 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 9 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
        st'.regs 10 = inp.dsHandlesAddr ctx.wd.W.m ∧ st'.regs 11 = hCur' ∧
        st'.regs 12 = i ∧
        Φ' = t2RoundPhi impl.pathDS kDel 32 45 (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
          (undel states') (vh states') (nodeRem (drainedAt (i + 1))) reps' st'.mem
    PTriple w p Pre
      (Stmt.loop (.reg 14) (
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
      )) (pNormalPost Post) (fun _ => 2) := by
  intro x drainedAt kDel undel vh nodeRem Pre Post
  set Lx := stc.L_inc x
  rcases drain_bounds ctx stc with ⟨h_v1, h_emb, h_hdl, h_ceb, h_vho, h_del, h_vh, h_vhd, h_vc, h_ps,
    h_ew, h_q, h_nlo, h_nds, h_dsc, h_stc, h_mhe, h_mwb, hW, _, _⟩
  have hx_sub := hS.hQ_sub x (List.getElem_mem hi)
  have hx_lt : x < inp.H'.n := hx_sub.1
  have hInc_x := hS.hInc x hx_lt
  let trueBr : Stmt :=
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
  let bodyStmt : Stmt :=
    Stmt.assign 15 (.load (.reg 14)) ;;
    Stmt.assign 16 (t2Ld (.reg 14) (.const 1)) ;;
    Stmt.assign 17 (t2Add (t2Ld (.reg 6) (.reg 15)) (.reg 16)) ;;
    Stmt.cond (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)) trueBr Stmt.nop ;;
    Stmt.assign 14 (t2Ld (.reg 14) (.const 2))
  let Inv : ℕ → State → ℕ → Prop := fun k st Φ =>
    k ≤ Lx.length ∧
    ∃ states reps hCur delCount,
      T2DrainInv ctx stc g₀ memStart (drainedAt i) states reps hCur delCount st.mem ∧
      IncChainBound st.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd (st.regs 14) (Lx.drop k) ∧
      (∀ idx (hidx : idx < Lx.length), idx < k →
        ∃ (hci : (Lx[idx]'hidx).1 < ctx.wd.comps.length),
          (Lx[idx]'hidx).2 < (ctx.wd.comps[(Lx[idx]'hidx).1]'hci).J_sub.m ∧
          (Lx[idx]'hidx).2 ∈ (states (Lx[idx]'hidx).1).deleted) ∧
      st.regs 0 = inp.v1 ∧ st.regs 2 = g₀.queue.length ∧ st.regs 3 = g₀.η₁ ∧
      st.regs 4 = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length ∧
      st.regs 5 = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length ∧
      st.regs 6 = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ∧
      st.regs 7 = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ∧
      st.regs 8 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
      st.regs 9 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length ∧
      st.regs 10 = inp.dsHandlesAddr ctx.wd.W.m ∧ st.regs 11 = hCur ∧
      st.regs 12 = i ∧ st.regs 13 = x ∧
      Φ = t2RoundPhi impl.pathDS kDel 32 45 (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
        (undel states) (vh states) (nodeRem (drainedAt (i + 1)) + (Lx.length - k)) reps st.mem
  have hloop := PTriple.loop_pot (w := w) (p := p) (α := ℕ) (e := .reg 14) (body := bodyStmt)
    (Inv := Inv) (Q := pNormalPost Post) (m := fun k => Lx.length - k) (rem := fun _ => 2)
    (condVal := fun st => st.regs 14)
    (fun _ _ _ _ => Expr.eval_reg_of_eq rfl)
    (fun k st Φ hI hz => by
      rcases hI with ⟨hk, states, reps, hCur, delCount, hD, hch, hdone,
        hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hΦ⟩
      have hnil : Lx.drop k = [] := by
        have haux : ∀ p L, IncChainBound st.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd p L →
            p = 0 → L = [] := fun p L h hp => by
          cases h with
          | nil => rfl
          | cons hlo => exact absurd hp (by omega)
        exact haux _ _ hch hz
      have hk_eq : k = Lx.length := by
        have hdrop := List.drop_eq_nil_iff.mp hnil
        omega
      have htake : g₀.queue.take (i + 1) = g₀.queue.take i ++ [x] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      have hmem_iff : ∀ y, y ∈ drainedAt (i + 1) ↔ y ∈ drainedAt i ∨ y = x := fun y => by
        simp only [drainedAt, htake, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.mem_union, Finset.mem_singleton]; tauto
      have hDr_next : T2DrainInv ctx stc g₀ memStart (drainedAt (i + 1)) states reps hCur delCount st.mem :=
        { hD with
          hDr_sub := fun y hy =>
            ((hmem_iff y).mp hy).elim (fun h => hD.hDr_sub h) (fun h => h ▸ hx_sub.2.1)
          hDr_del := fun y hy hyn ci' hci' b' hb' hyb => by
            rcases (hmem_iff y).mp hy with hy_i | rfl
            · exact hD.hDr_del y hy_i hyn ci' hci' b' hb' hyb
            · obtain ⟨idx, hidx_len, hidx_eq⟩ := List.getElem_of_mem (hInc_x.2.2 ci' hci' b' hb' hyb)
              obtain ⟨_, _, hdel⟩ := hdone idx hidx_len (hk_eq ▸ hidx_len)
              rw [hidx_eq] at hdel; exact hdel }
      refine ⟨⟨states, reps, hCur, delCount, hDr_next,
        hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, ?_⟩, by simp [Expr.size]⟩
      simpa [hk_eq] using hΦ)
    (fun k st Φ ω hI hnz => by
        rcases hI with ⟨hk, states, reps, hCur, delCount, hD, hch, hdone,
          hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hΦ⟩
        have hinv : ∀ p L, IncChainBound st.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd p L →
            p ≠ 0 → ∃ ci b next rest, L = (ci, b) :: rest ∧
              inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ p ∧ p + 2 < stc.nodesEnd ∧
              st.mem p = ci ∧ st.mem (p + 1) = b ∧ st.mem (p + 2) = next ∧
              IncChainBound st.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd next rest := by
          intro p L h hp
          cases h with
          | nil => exact absurd rfl hp
          | cons hlo hhi m0 m1 m2 hrest => exact ⟨_, _, _, _, rfl, hlo, hhi, m0, m1, m2, hrest⟩
        obtain ⟨ci, b, next, rest, heq_drop, hptr_lo, hptr_hi, hm0, hm1, hm2, hch_rest⟩ :=
          hinv _ _ hch hnz
        have _ := hptr_lo
        have _ := hptr_hi
        have hk_lt : k < Lx.length := by
          have : (Lx.drop k).length = ((ci, b) :: rest).length := congrArg List.length heq_drop
          rw [List.length_drop, List.length_cons] at this; omega
        have hLx_k : Lx[k]'hk_lt = (ci, b) := by
          have := List.getElem_cons_drop hk_lt
          rw [heq_drop] at this; exact (List.cons.inj this).1
        have hdrop_succ : Lx.drop (k + 1) = rest := by
          have := List.getElem_cons_drop hk_lt
          rw [heq_drop] at this; exact (List.cons.inj this).2
        obtain ⟨hci, hb_m, hx_in⟩ := hInc_x.2.1 (ci, b) (hLx_k ▸ List.getElem_mem hk_lt)
        dsimp only at hci hb_m hx_in
        set ptr := st.regs 14
        have hptr_eq : st.regs 14 = ptr := rfl
        have hs1 : Runs w p ω (Stmt.assign 15 (.load (.reg 14))) st .normal
            { st with regs := Function.update st.regs 15 ci } 3 :=
          runs_assign_iff.mpr ⟨ci, by simpa [hm0] using Expr.eval_load (Expr.eval_reg_of_eq hptr_eq),
            rfl, rfl, by simp [Expr.size]⟩
        set st1 : State := { st with regs := Function.update st.regs 15 ci }
        have hs2 : Runs w p ω (Stmt.assign 16 (t2Ld (.reg 14) (.const 1))) st1 .normal
            { st1 with regs := Function.update st1.regs 16 b } 5 := by
          have hr14_1 : st1.regs 14 = ptr := by dsimp only [st1]; rw [Function.update_of_ne (by omega)]
          have hptr1_w : ptr + 1 < 2 ^ w := by omega
          have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr14_1) (Expr.eval_const hW) hptr1_w
          exact runs_assign_iff.mpr ⟨b, by simpa [t2Ld, st1, hm1] using Expr.eval_load (w := w) ha,
            rfl, rfl, by simp [Expr.size]⟩
        set st2 : State := { st1 with regs := Function.update st1.regs 16 b }
        have hceb_ci : st2.mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) =
            compEdgeBase ctx.wd ci :=
          (hD.hAgr _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hS.hCeb ci hci)
        have hsum_j : compEdgeBase ctx.wd ci + b < inp.J.m := by
          have ha1 := compEdgeBase_add_le hci
          have ha2 := compEdgeBase_le_sum (wd := ctx.wd) (by omega : ci + 1 ≤ ctx.wd.comps.length); omega
        have hs3 : Runs w p ω (Stmt.assign 17 (t2Add (t2Ld (.reg 6) (.reg 15)) (.reg 16))) st2 .normal
            { st2 with regs := Function.update st2.regs 17 (compEdgeBase ctx.wd ci + b) } 7 := by
          have hr6_2 : st2.regs 6 = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length := by
            dsimp only [st2, st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hr6
          have hr15_2 : st2.regs 15 = ci := by
            dsimp only [st2, st1]; rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
          have hr16_2 : st2.regs 16 = b := by dsimp only [st2]; exact Function.update_self _ _ _
          have hceb_w : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci < 2 ^ w := by omega
          have hsum_w : compEdgeBase ctx.wd ci + b < 2 ^ w := by omega
          have hld := Expr.eval_load (w := w)
            (Expr.eval_add (w := w) (Expr.eval_reg_of_eq hr6_2) (Expr.eval_reg_of_eq hr15_2) hceb_w)
          rw [show st2.mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) = compEdgeBase ctx.wd ci from hceb_ci] at hld
          exact runs_assign_iff.mpr ⟨compEdgeBase ctx.wd ci + b,
            Expr.eval_add (w := w) hld (Expr.eval_reg_of_eq hr16_2) hsum_w,
            rfl, rfl, by simp [Expr.size]⟩
        set st3 : State := { st2 with regs := Function.update st2.regs 17 (compEdgeBase ctx.wd ci + b) }
        have hr3_eq : ∀ r ≤ 14, st3.regs r = st.regs r := fun r hr => by
          dsimp only [st3, st2, st1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        set delV := st.mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b)
        have hdelV_le : delV ≤ g₀.η₁ := (hD.hDelR ci hci b hb_m).1
        have he_cond : (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)).eval w st3 =
            some (if delV < g₀.η₁ then 1 else 0) := by
          have hr17_3 : st3.regs 17 = compEdgeBase ctx.wd ci + b := by
            dsimp only [st3]; exact Function.update_self _ _ _
          have hdel_w : inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + (compEdgeBase ctx.wd ci + b) < 2 ^ w := by
            omega
          have ha := Expr.eval_add (w := w) (Expr.eval_reg_of_eq ((hr3_eq 7 (by omega)).trans hr7))
            (Expr.eval_reg_of_eq hr17_3) hdel_w
          have hld : (t2Ld (.reg 7) (.reg 17)).eval w st3 = some delV := by
            simpa [t2Ld, st3, st2, st1, delV, Nat.add_assoc] using Expr.eval_load (w := w) ha
          exact Expr.eval_lt_op hld (Expr.eval_reg_of_eq ((hr3_eq 3 (by omega)).trans hr3)) hW
        have hnext_w : ∀ {mem' : ℕ → ℕ}, IncChainBound mem' (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd next rest → next < 2 ^ w := by
          intro mem' hch'; cases hch' with | nil => omega | cons hlo => omega
        by_cases hlt : delV < g₀.η₁
        · have he_c1 : (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)).eval w st3 = some 1 := by simpa [hlt] using he_cond
          obtain ⟨st_tr, c_tr, states', reps', hCur', hr_tr, htr_regs, htr11, hdel_mono, hD',
              hb_in', hch_rest', hΦ_tr⟩ :=
            t2Drain_node_true_step ctx stc hSpec hS hi (st := st3) hD hci hb_m hx_in hlt hch_rest
              ((hr3_eq 0 (by omega)).trans hr0) ((hr3_eq 3 (by omega)).trans hr3)
              ((hr3_eq 7 (by omega)).trans hr7) ((hr3_eq 8 (by omega)).trans hr8)
              ((hr3_eq 9 (by omega)).trans hr9) ((hr3_eq 10 (by omega)).trans hr10)
              ((hr3_eq 11 (by omega)).trans hr11)
              (by dsimp only [st3, st2, st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact Function.update_self _ _ _)
              (by dsimp only [st3, st2]; rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _)
              (by dsimp only [st3]; exact Function.update_self _ _ _) (ω := ω)
          have hcond_runs : Runs w p ω (Stmt.cond (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)) trueBr Stmt.nop)
              st3 .normal st_tr (6 + c_tr + 1) :=
            runs_cond_iff.mpr ⟨1, c_tr, he_c1, by simpa [trueBr] using hr_tr, by simp [Expr.size]⟩
          have hm2_tr : st_tr.mem (ptr + 2) = next := by
            rw [hD'.hAgr _ (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact (hD.hAgr _ (by omega) (by omega) (by omega) (by omega) (by omega)).symm.trans hm2
          have hnw : next < 2 ^ w := hnext_w hch_rest'
          have hs5 : Runs w p ω (Stmt.assign 14 (t2Ld (.reg 14) (.const 2))) st_tr .normal
              { st_tr with regs := Function.update st_tr.regs 14 next } 5 := by
            have ha := Expr.eval_add (Expr.eval_reg_of_eq ((htr_regs 14 (by omega) (by omega)).trans ((hr3_eq 14 (by omega)).trans hptr_eq)))
              (Expr.eval_const (by omega : 2 < 2 ^ w)) (by omega)
            exact runs_assign_iff.mpr ⟨next, by simpa [t2Ld, hm2_tr] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
          have hbody_runs : Runs w p ω bodyStmt st .normal
              { st_tr with regs := Function.update st_tr.regs 14 next }
              (3 + 1 + 5 + 1 + 7 + 1 + (6 + c_tr + 1) + 1 + 5) :=
            runs_seq_iff.mpr (Or.inr ⟨st1, 3, 5 + (7 + ((6 + c_tr + 1) + 5 + 1) + 1) + 1, hs1,
              runs_seq_iff.mpr (Or.inr ⟨st2, 5, 7 + ((6 + c_tr + 1) + 5 + 1) + 1, hs2,
                runs_seq_iff.mpr (Or.inr ⟨st3, 7, (6 + c_tr + 1) + 5 + 1, hs3,
                  runs_seq_iff.mpr (Or.inr ⟨st_tr, 6 + c_tr + 1, 5, hcond_runs, hs5, rfl⟩),
                  rfl⟩), rfl⟩), by omega⟩)
          set stF : State := { st_tr with regs := Function.update st_tr.regs 14 next }
          have hstF_r : ∀ r ≤ 13, r ≠ 11 → stF.regs r = st.regs r := fun r hr hne => by
            dsimp only [stF]; rw [Function.update_of_ne (by omega), htr_regs r (by omega) hne, hr3_eq r (by omega)]
          have hDone' : ∀ idx (hidx : idx < Lx.length), idx < k + 1 →
              ∃ (hci'' : (Lx[idx]'hidx).1 < ctx.wd.comps.length),
                (Lx[idx]'hidx).2 < (ctx.wd.comps[(Lx[idx]'hidx).1]'hci'').J_sub.m ∧
                (Lx[idx]'hidx).2 ∈ (states' (Lx[idx]'hidx).1).deleted := fun idx hidx _ => by
            by_cases hlt_k : idx < k
            · obtain ⟨hci'', hbm'', hdel''⟩ := hdone idx hidx hlt_k
              exact ⟨hci'', hbm'', hdel_mono _ hdel''⟩
            · have heq : idx = k := by omega
              subst heq; refine ⟨by simp [hLx_k, hci], by simp [hLx_k, hb_m], ?_⟩
              simpa [hLx_k] using hb_in'
          refine ⟨.normal, stF, _, _, hbody_runs, k + 1,
            ⟨by omega, states', reps', hCur', delCount + 1, hD', by simpa [stF, hdrop_succ] using hch_rest', hDone',
              (hstF_r 0 (by omega) (by omega)).trans hr0, (hstF_r 2 (by omega) (by omega)).trans hr2,
              (hstF_r 3 (by omega) (by omega)).trans hr3, (hstF_r 4 (by omega) (by omega)).trans hr4,
              (hstF_r 5 (by omega) (by omega)).trans hr5, (hstF_r 6 (by omega) (by omega)).trans hr6,
              (hstF_r 7 (by omega) (by omega)).trans hr7, (hstF_r 8 (by omega) (by omega)).trans hr8,
              (hstF_r 9 (by omega) (by omega)).trans hr9, (hstF_r 10 (by omega) (by omega)).trans hr10,
              by dsimp only [stF]; rw [Function.update_of_ne (by omega)]; exact htr11,
              (hstF_r 12 (by omega) (by omega)).trans hr12, (hstF_r 13 (by omega) (by omega)).trans hr13, rfl⟩,
            by omega, ?_⟩
          rw [hΦ]
          have hrem : Lx.length - k = (Lx.length - (k + 1)) + 1 := by omega
          have hmul : (nodeRem (drainedAt (i + 1)) + (Lx.length - k)) * 45 =
              (nodeRem (drainedAt (i + 1)) + (Lx.length - (k + 1))) * 45 + 45 := by
            rw [hrem, ← add_assoc, Nat.add_mul, Nat.one_mul]
          dsimp only [t2RoundPhi, Expr.size, undel, vh, stF, st3, st2, st1, kDel] at hΦ_tr ⊢
          rw [hmul] at ⊢
          omega
        · have he_c0 : (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)).eval w st3 = some 0 := by simpa [hlt] using he_cond
          have hcond_runs : Runs w p ω (Stmt.cond (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)) trueBr Stmt.nop)
              st3 .normal st3 (6 + 1 + 1) :=
            runs_cond_iff.mpr ⟨0, 1, he_c0, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
          have hnw : next < 2 ^ w := hnext_w hch_rest
          have hs5 : Runs w p ω (Stmt.assign 14 (t2Ld (.reg 14) (.const 2))) st3 .normal
              { st3 with regs := Function.update st3.regs 14 next } 5 := by
            have ha := Expr.eval_add (Expr.eval_reg_of_eq ((hr3_eq 14 (by omega)).trans hptr_eq)) (Expr.eval_const (by omega : 2 < 2 ^ w)) (by omega)
            exact runs_assign_iff.mpr ⟨next, by simpa [t2Ld, st3, st2, st1, hm2] using Expr.eval_load ha, rfl, rfl, by simp [Expr.size]⟩
          have hbody_runs : Runs w p ω bodyStmt st .normal
              { st3 with regs := Function.update st3.regs 14 next }
              (3 + 1 + 5 + 1 + 7 + 1 + (6 + 1 + 1) + 1 + 5) :=
            runs_seq_iff.mpr (Or.inr ⟨st1, 3, 5 + (7 + ((6 + 1 + 1) + 5 + 1) + 1) + 1, hs1,
              runs_seq_iff.mpr (Or.inr ⟨st2, 5, 7 + ((6 + 1 + 1) + 5 + 1) + 1, hs2,
                runs_seq_iff.mpr (Or.inr ⟨st3, 7, (6 + 1 + 1) + 5 + 1, hs3,
                  runs_seq_iff.mpr (Or.inr ⟨st3, 6 + 1 + 1, 5, hcond_runs, hs5, rfl⟩),
                  rfl⟩), rfl⟩), by omega⟩)
          set stF : State := { st3 with regs := Function.update st3.regs 14 next }
          have hstF_r : ∀ r ≤ 13, stF.regs r = st.regs r := fun r hr => by
            dsimp only [stF]; rw [Function.update_of_ne (by omega), hr3_eq r (by omega)]
          have hb_del : b ∈ (states ci).deleted := ((hD.hDelR ci hci b hb_m).2).mp (by omega)
          have hDone' : ∀ idx (hidx : idx < Lx.length), idx < k + 1 →
              ∃ (hci'' : (Lx[idx]'hidx).1 < ctx.wd.comps.length),
                (Lx[idx]'hidx).2 < (ctx.wd.comps[(Lx[idx]'hidx).1]'hci'').J_sub.m ∧
                (Lx[idx]'hidx).2 ∈ (states (Lx[idx]'hidx).1).deleted := fun idx hidx _ => by
            by_cases hlt_k : idx < k
            · exact hdone idx hidx hlt_k
            · have heq : idx = k := by omega
              subst heq; refine ⟨by simp [hLx_k, hci], by simp [hLx_k, hb_m], ?_⟩
              simpa [hLx_k] using hb_del
          refine ⟨.normal, stF, _, _, hbody_runs, k + 1,
            ⟨by omega, states, reps, hCur, delCount, hD, by simpa [stF, st3, st2, st1, hdrop_succ] using hch_rest, hDone',
              (hstF_r 0 (by omega)).trans hr0, (hstF_r 2 (by omega)).trans hr2,
              (hstF_r 3 (by omega)).trans hr3, (hstF_r 4 (by omega)).trans hr4,
              (hstF_r 5 (by omega)).trans hr5, (hstF_r 6 (by omega)).trans hr6,
              (hstF_r 7 (by omega)).trans hr7, (hstF_r 8 (by omega)).trans hr8,
              (hstF_r 9 (by omega)).trans hr9, (hstF_r 10 (by omega)).trans hr10,
              (hstF_r 11 (by omega)).trans hr11, (hstF_r 12 (by omega)).trans hr12,
              (hstF_r 13 (by omega)).trans hr13, rfl⟩,
            by omega, ?_⟩
          rw [hΦ]
          have hrem : Lx.length - k = (Lx.length - (k + 1)) + 1 := by omega
          have hmul : (nodeRem (drainedAt (i + 1)) + (Lx.length - k)) * 45 =
              (nodeRem (drainedAt (i + 1)) + (Lx.length - (k + 1))) * 45 + 45 := by
            rw [hrem, ← add_assoc, Nat.add_mul, Nat.one_mul]
          dsimp only [t2RoundPhi, Expr.size, stF, st3, st2, st1] at ⊢
          rw [hmul]
          omega)
    0
  refine PTriple.conseq hloop (fun st Φ hPre => ?_) (fun o st' Φ' hQ => hQ) (fun _ _ _ => le_refl _)
  rcases hPre with ⟨states, reps, hCur, delCount, hD, hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9,
    hr10, hr11, hr12, hr13, hr14, hΦ⟩
  have hch0 : IncChainBound st.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
      (st.regs 14) Lx := by
    rw [hr14, hD.hAgr _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hInc_x.1.mono fun a ha1 ha2 =>
      hD.hAgr a (by omega) (by omega) (by omega) (by omega) (by omega)
  have hsplit := drain_nodeRem_split stc.L_inc g₀.drained g₀.queue hS.hQ_nd
    (fun y hy => ⟨(hS.hQ_sub y hy).1, (hS.hQ_sub y hy).2.2⟩) hi
  refine ⟨Nat.zero_le _, states, reps, hCur, delCount, hD, by simpa using hch0, fun _ _ hidx => by omega,
    hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, ?_⟩
  dsimp only [t2RoundPhi, nodeRem, drainedAt] at hΦ ⊢
  dsimp only at hsplit
  rw [hΦ, hsplit, Nat.sub_zero, add_comm (Lx.length)]

end MinCostFlow.Spanner
