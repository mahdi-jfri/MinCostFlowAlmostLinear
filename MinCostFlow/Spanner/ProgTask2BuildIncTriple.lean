module

public import MinCostFlow.Spanner.ProgTask2BuildIncProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Outer loop and full `t2BuildInc_triple` specification -/

private lemma t2BuildInc_outer_step {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T2Ctx impl inp mem₀ w) {memStart : ℕ → ℕ}
    {ci : ℕ} (hci : ci < ctx.wd.comps.length)
    (hEmbStart : EmbAt memStart inp.embJHAddr inp.J.m inp.embJH)
    (hEmbBnd : EmbBounded memStart inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr)
    (hCompsStart : CompsDoneUpTo ctx.wInp.prep memStart ctx.wInp.prep.rawComps.length)
    (hW : 1 < 2 ^ w) (hMax : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum < 2 ^ w) :
    let cJm := ctx.wd.comps[ci].J_sub.m
    Triple w p
      (fun st => T2IncInv ctx memStart ci ci 0 0 st ∧ st.regs 12 = ci)
      (t2St (.reg 5) (.reg 12) (.reg 9) ;;
       t2St (.reg 6) (.reg 12) (.reg 10) ;;
       Stmt.assign 13 (t2Add (.reg 4) (t2Mul (.const 7) (.reg 12))) ;;
       Stmt.assign 14 (t2Ld (.reg 13) (.const 1)) ;;
       Stmt.assign 15 (t2Ld (.reg 13) (.const 4)) ;;
       Stmt.assign 16 (t2Ld (.reg 13) (.const 6)) ;;
       Stmt.assign 9 (t2Add (.reg 9) (.reg 16)) ;;
       Stmt.assign 10 (t2Add (.reg 10) (.reg 14)) ;;
       forRange 17 (.const 0) (.reg 16) (
         Stmt.assign 18 (t2Ld (.reg 15) (.reg 17)) ;;
         Stmt.assign 19 (t2Ld (.reg 7) (.reg 18)) ;;
         Stmt.assign 20 (.load (.reg 19)) ;;
         forRange 21 (.const 0) (.reg 20) (
           Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
           Stmt.assign 23 (t2Ld (.reg 8) (.reg 22)) ;;
           Stmt.store (.reg 11) (.reg 12) ;;
           t2St (.reg 11) (.const 1) (.reg 17) ;;
           t2St (.reg 11) (.const 2) (.reg 23) ;;
           t2St (.reg 8) (.reg 22) (.reg 11) ;;
           Stmt.assign 11 (t2Add (.reg 11) (.const 3))
         )
       ))
      (normalPost fun st₁ =>
        T2IncInv ctx memStart (ci + 1) (ci + 1) 0 0
          { st₁ with regs := Function.update st₁.regs 12 (ci + 1) } ∧ st₁.regs 12 = ci)
      (fun _ => (∑ b ∈ Finset.range cJm,
        ((inp.embJH (ctx.wd.comps[ci].jSubOrigEdges.getD b 0)).verts.length * 49 + 32)) + 54) := by
  intro cJm st ω ⟨hinv, hr12⟩
  rcases hinv with ⟨hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hptr_lo, hptr_hi, hzf,
    hfr, hceb, hvho, hInc⟩
  set mW := ctx.wd.W.m
  set K := ctx.wd.comps.length
  set eb := compEdgeBase ctx.wd ci
  set vo := vhatBase ctx.wd ci
  have hlen := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hci_r : ci < ctx.wInp.prep.rawComps.length := by
    change ci < (ctx.wInp.buildCompsFrom _ _ _).length at hci; omega
  have hchain := t2_prep_chain_bounds ctx
  have hdisj : inp.v1 + 32 ≤ inp.compEdgeBaseAddr mW K ∧
      inp.compEdgeBaseAddr mW K + K = inp.vhatOffsetAddr mW K ∧
      inp.vhatOffsetAddr mW K + K = inp.compEdgeDelRoundAddr mW K ∧
      inp.compEdgeDelRoundAddr mW K ≤ inp.vHeadAddr mW K ∧
      inp.vHeadAddr mW K + inp.H'.n ≤ inp.nodesAddr mW K ∧
      2 * inp.J.m ≤ inp.nodesAddr mW K ∧ inp.H'.n ≤ inp.nodesAddr mW K :=
    t2_v1_le_compEdgeBase ctx
  have hnodes_lt_w : inp.nodesAddr mW K + 3 * inp.embVertSum < 2 ^ w := hMax
  have hprep_ptrs := t2_prep_comp_ptrs_le ctx hci
  have hSumJ : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m := by
    have h := mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
    change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ ctx.wInp.prep.J.m at h
    rw [ctx.hWInpJ] at h; omega
  have heb_next : eb + cJm = compEdgeBase ctx.wd (ci + 1) := compEdgeBase_add_le hci
  have hvo_next : vo + ctx.wd.comps[ci].J_sub.n = vhatBase ctx.wd (ci + 1) := vhatBase_add_le hci
  have heb_le : eb + cJm ≤ inp.J.m := le_trans (by rw [heb_next]; exact compEdgeBase_le_sum (by omega)) hSumJ
  have hvo_le : vo + ctx.wd.comps[ci].J_sub.n ≤ 2 * inp.J.m := by
    rw [hvo_next]
    exact le_trans (vhatBase_le_sum (Nat.succ_le_of_lt hci)) ctx.hvhatSum_le
  have hmJ_w : 2 * inp.J.m < 2 ^ w := by omega
  suffices hres : ∃ o st' c, Runs w p ω
      (t2St (.reg 5) (.reg 12) (.reg 9) ;;
       t2St (.reg 6) (.reg 12) (.reg 10) ;;
       Stmt.assign 13 (t2Add (.reg 4) (t2Mul (.const 7) (.reg 12))) ;;
       Stmt.assign 14 (t2Ld (.reg 13) (.const 1)) ;;
       Stmt.assign 15 (t2Ld (.reg 13) (.const 4)) ;;
       Stmt.assign 16 (t2Ld (.reg 13) (.const 6)) ;;
       Stmt.assign 9 (t2Add (.reg 9) (.reg 16)) ;;
       Stmt.assign 10 (t2Add (.reg 10) (.reg 14)) ;;
       forRange 17 (.const 0) (.reg 16) (
         Stmt.assign 18 (t2Ld (.reg 15) (.reg 17)) ;;
         Stmt.assign 19 (t2Ld (.reg 7) (.reg 18)) ;;
         Stmt.assign 20 (.load (.reg 19)) ;;
         forRange 21 (.const 0) (.reg 20) (
           Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
           Stmt.assign 23 (t2Ld (.reg 8) (.reg 22)) ;;
           Stmt.store (.reg 11) (.reg 12) ;;
           t2St (.reg 11) (.const 1) (.reg 17) ;;
           t2St (.reg 11) (.const 2) (.reg 23) ;;
           t2St (.reg 8) (.reg 22) (.reg 11) ;;
           Stmt.assign 11 (t2Add (.reg 11) (.const 3))
         )
       )) st o st' c ∧
      normalPost (fun st₁ =>
        T2IncInv ctx memStart (ci + 1) (ci + 1) 0 0
          { st₁ with regs := Function.update st₁.regs 12 (ci + 1) } ∧ st₁.regs 12 = ci) o st' ∧
      0 + c ≤ (∑ b ∈ Finset.range cJm,
        ((inp.embJH (ctx.wd.comps[ci].jSubOrigEdges.getD b 0)).verts.length * 49 + 32)) + 54 by
    simpa only [Nat.zero_add] using hres
  refine runs_seq_store_le (x := inp.compEdgeBaseAddr mW K + ci) (v := eb)
    (ev_add (ev_reg hr5 (by omega)) (ev_reg hr12 (by omega)) (by omega))
    (ev_reg hr9 (by omega)) ?_
  set m1 := Function.update st.mem (inp.compEdgeBaseAddr mW K + ci) eb
  refine runs_seq_store_le (x := inp.vhatOffsetAddr mW K + ci) (v := vo)
    (ev_add (ev_reg hr6 (by omega)) (ev_reg hr12 (by omega)) (by omega))
    (ev_reg hr10 (by omega)) ?_
  set m2 := Function.update m1 (inp.vhatOffsetAddr mW K + ci) vo
  have hfr2 : T2BuildIncFrame ctx memStart m2 :=
    t2BuildIncFrame_upd_vhatOffset ctx (t2BuildIncFrame_upd_compEdgeBase ctx hfr hci) hci
  have hm2_agr : ∀ a < ctx.wInp.prep.hEnd, m2 a = memStart a := fun a ha =>
    hfr2 a (Or.inl (show a < inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length by
      change a < inp.compEdgeBaseAddr mW K; omega))
  have hm2_13 : m2 (ctx.wInp.prep.aComps + 7 * ci + 1) = ctx.wd.comps[ci].J_sub.n := by
    rw [hm2_agr _ (by omega)]
    have hcomp := hCompsStart ci hci_r
    have hcard := (t2_prep_cJSub_m_eq ctx hci).2.2
    have hJn : ctx.wd.comps[ci].J_sub.n = ctx.wd.comps[ci].X.card :=
      (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.1
    rw [hJn, hcard]
    simpa [getElem!_pos ctx.wInp.prep.rawComps ci hci_r] using hcomp.2.1
  have hm2_15 : m2 (ctx.wInp.prep.aComps + 7 * ci + 4) = ctx.wInp.prep.cJOrigPtr ci := by
    rw [hm2_agr _ (by omega)]; exact (hCompsStart ci hci_r).2.2.2.2.1
  have hm2_16 : m2 (ctx.wInp.prep.aComps + 7 * ci + 6) = cJm := by
    rw [hm2_agr _ (by omega)]
    have hrc_eq := getElem!_pos ctx.wInp.prep.rawComps ci hci_r
    dsimp only [cJm]
    rw [(t2_prep_cJSub_m_eq ctx hci).1, ← hrc_eq]
    exact (hCompsStart ci hci_r).2.2.2.2.2.2.1
  refine runs_seq_assign_le (v := ctx.wInp.prep.aComps + 7 * ci)
    (ev_add (ev_reg hr4 (by omega))
      (ev_mul (ev_const (w := w) (by omega)) (ev_reg hr12 (by omega)) (by omega)) (by omega)) ?_
  set r13 := Function.update st.regs 13 (ctx.wInp.prep.aComps + 7 * ci)
  refine runs_seq_assign_le (v := ctx.wd.comps[ci].J_sub.n)
    (ev_load (ev_add (ev_reg (r := 13) (by simp [r13]) (by omega)) (ev_const hW) (by omega))
      hm2_13 (by omega)) ?_
  set r14 := Function.update r13 14 ctx.wd.comps[ci].J_sub.n
  refine runs_seq_assign_le (v := ctx.wInp.prep.cJOrigPtr ci)
    (ev_load (ev_add (ev_reg (r := 13) (by simp [r14, r13]) (by omega))
      (ev_const (w := w) (by omega)) (by omega)) hm2_15 (by omega)) ?_
  set r15 := Function.update r14 15 (ctx.wInp.prep.cJOrigPtr ci)
  refine runs_seq_assign_le (v := cJm)
    (ev_load (ev_add (ev_reg (r := 13) (by simp [r15, r14, r13]) (by omega))
      (ev_const (w := w) (by omega)) (by omega)) hm2_16 (by omega)) ?_
  set r16 := Function.update r15 16 cJm
  refine runs_seq_assign_le (v := eb + cJm)
    (ev_add (ev_reg (r := 9) (by simp [r16, r15, r14, r13, hr9]) (by omega))
      (ev_reg (r := 16) (by simp [r16]) (by omega)) (by omega)) ?_
  rw [heb_next]
  set r9' := Function.update r16 9 (compEdgeBase ctx.wd (ci + 1))
  refine runs_seq_assign_le (v := vo + ctx.wd.comps[ci].J_sub.n)
    (ev_add (ev_reg (r := 10) (by simp [r9', r16, r15, r14, r13, hr10]) (by omega))
      (ev_reg (r := 14) (by simp [r9', r16, r15, r14]) (by omega)) (by omega)) ?_
  rw [hvo_next]
  set r10' := Function.update r9' 10 (vhatBase ctx.wd (ci + 1))
  have hzf2 : ZeroFrom m2 (st.regs 11) := fun a ha => by
    simp only [m2, m1,
      Function.update_of_ne (by omega : a ≠ inp.vhatOffsetAddr mW K + ci),
      Function.update_of_ne (by omega : a ≠ inp.compEdgeBaseAddr mW K + ci)]
    exact hzf a ha
  have hceb2 : ∀ c < ci + 1, m2 (inp.compEdgeBaseAddr mW K + c) = compEdgeBase ctx.wd c := fun c hc => by
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hc) with hlt | rfl
    · simp only [m2, m1,
        Function.update_of_ne (by omega : inp.compEdgeBaseAddr mW K + c ≠ inp.vhatOffsetAddr mW K + ci),
        Function.update_of_ne (by omega : inp.compEdgeBaseAddr mW K + c ≠ inp.compEdgeBaseAddr mW K + ci)]
      exact hceb c hlt
    · dsimp only [m2, m1, eb]
      rw [Function.update_of_ne (by omega), Function.update_self]
  have hvho2 : ∀ c < ci + 1, m2 (inp.vhatOffsetAddr mW K + c) = vhatBase ctx.wd c := fun c hc => by
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hc) with hlt | rfl
    · simp only [m2, m1,
        Function.update_of_ne (by omega : inp.vhatOffsetAddr mW K + c ≠ inp.vhatOffsetAddr mW K + ci),
        Function.update_of_ne (by omega : inp.vhatOffsetAddr mW K + c ≠ inp.compEdgeBaseAddr mW K + ci)]
      exact hvho c hlt
    · dsimp only [m2, m1, vo]
      rw [Function.update_self]
  have hInc2 : IncListForPairs m2 (inp.vHeadAddr mW K) inp.H'.n ctx.wd.comps inp.embJH
      (inp.nodesAddr mW K) (st.regs 11) (t2DonePred ctx.wd.comps inp.embJH ci 0 0) :=
    incListForPairs_mono hInc
      (fun x _ => by
        simp only [m2, m1,
          Function.update_of_ne (by omega : inp.vHeadAddr mW K + x ≠ inp.vhatOffsetAddr mW K + ci),
          Function.update_of_ne (by omega : inp.vHeadAddr mW K + x ≠ inp.compEdgeBaseAddr mW K + ci)])
      (fun a ha_lo _ => by
        simp only [m2, m1,
          Function.update_of_ne (by omega : a ≠ inp.vhatOffsetAddr mW K + ci),
          Function.update_of_ne (by omega : a ≠ inp.compEdgeBaseAddr mW K + ci)])
      (fun _ _ _ h => h)
  let InvB := fun b (s : State) =>
    T2IncInv ctx memStart (ci + 1) ci b 0 s ∧
    s.regs 12 = ci ∧ s.regs 15 = ctx.wInp.prep.cJOrigPtr ci ∧ s.regs 16 = cJm ∧ s.regs 17 = b
  let sc := fun b => 49 * (inp.embJH (ctx.wd.comps[ci].jSubOrigEdges.getD b 0)).verts.length + 23
  have hloop := Triple.forRange_le (p := p) (P := fun st_ => st_ = { st with regs := r10', mem := m2 })
    (Inv := InvB) sc 0 cJm (Nat.zero_le _) hW (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨ev_const (Nat.zero_lt_of_lt hW), ?_, by simp [r10', r9', r16, r15, r14, r13, hr12],
        by simp [r10', r9', r16, r15], by simp [r10', r9', r16], rfl⟩
      refine ⟨by simp [r10', r9', r16, r15, r14, r13, hr0],
        by simp [r10', r9', r16, r15, r14, r13, hr2],
        by simpa [r10', r9', r16, r15, r14, r13] using hr3,
        by simp [r10', r9', r16, r15, r14, r13, hr4],
        by simpa [r10', r9', r16, r15, r14, r13] using hr5,
        by simpa [r10', r9', r16, r15, r14, r13] using hr6,
        by simp [r10', r9', r16, r15, r14, r13, hr7],
        by simpa [r10', r9', r16, r15, r14, r13] using hr8,
        by simp [r10', r9'], by simp [r10'],
        hptr_lo, hptr_hi, hzf2, hfr2, hceb2, hvho2, hInc2⟩)
    (fun b s _ _ h => h.2.2.2.2)
    (fun b s _ _ h => ev_reg h.2.2.2.1 (by omega))
    (fun b _ hb => (t2BuildInc_mid_step ctx hci hb hEmbStart hEmbBnd hCompsStart hW hMax).conseq
      (fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩)
      (fun o s ho => by
        cases o with
        | returned _ => exact False.elim ho
        | normal =>
          rcases ho with ⟨⟨ha, hb12, hb15, hb16⟩, hr17b⟩
          exact ⟨⟨ha, hb12, hb15, hb16, by simp⟩, hr17b⟩)
      (fun _ _ => le_refl _))
  obtain ⟨o, st₁, c_loop, hr_loop, hq_loop, hc_loop⟩ := hloop { st with regs := r10', mem := m2 } ω rfl
  cases o with
  | returned _ => exact False.elim hq_loop
  | normal =>
    rcases hq_loop with ⟨⟨h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, hlo, hhi, hzf', hfr', hceb',
      hvho', hInc'⟩, h12, _, _, _⟩
    have hcost_sum : rangeCost sc 0 cJm + cJm * 9 + 7 =
        (∑ b ∈ Finset.range cJm,
          ((inp.embJH (ctx.wd.comps[ci].jSubOrigEdges.getD b 0)).verts.length * 49 + 32)) + 7 := by
      rw [rangeCost_zero_eq_sum]
      have h1 : ∑ b ∈ Finset.range cJm,
            (49 * (inp.embJH (ctx.wd.comps[ci].jSubOrigEdges.getD b 0)).verts.length + 23) + cJm * 9 + 7 =
          ∑ b ∈ Finset.range cJm,
            ((inp.embJH (ctx.wd.comps[ci].jSubOrigEdges.getD b 0)).verts.length * 49 + 32) + 7 := by
        rw [Finset.sum_add_distrib, show cJm * 9 = ∑ _ ∈ Finset.range cJm, 9 by simp,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        congr 1; refine Finset.sum_congr rfl fun b _ => by ring
      exact h1
    simp only [Expr.size] at hc_loop ⊢
    refine ⟨.normal, st₁, c_loop, hr_loop, ?_, by omega⟩
    refine ⟨⟨by simp [h0], by simp [h2], by simpa using h3, by simp [h4], by simpa using h5,
      by simpa using h6, by simp [h7], by simpa using h8, by simp [h9], by simp [h10], hlo, ?_,
      hzf', hfr', hceb', hvho', ?_⟩, h12⟩
    · dsimp only [cJm] at hhi; simpa [t2PrefixVerts_comp_end hci] using hhi
    · exact incListForPairs_mono hInc' (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ _ hp => t2DonePred_ci_step hci hp)

/-- Full specification triple for `t2BuildIncBody` (`[v1, nodesAddr] → nodesEnd`). -/
theorem t2BuildInc_triple {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ memStart : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T2Ctx impl inp mem₀ w)
    (hAgr0 : ∀ x < inp.v1, memStart x = mem₀ x)
    (h12 : memStart (inp.v1 + 12) = inp.embJHAddr)
    (h13 : memStart (inp.v1 + 13) = ctx.wInp.prep.h)
    (h16 : memStart (inp.v1 + 16) = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length)
    (h17 : memStart (inp.v1 + 17) = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
    (h20 : memStart (inp.v1 + 20) = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length)
    (hzf0 : ZeroFrom memStart (inp.v1 + 32)) :
    let mW := ctx.wd.W.m
    let K := ctx.wd.comps.length
    let nodesAddr := inp.nodesAddr mW K
    Triple w p
      (fun st => st.regs 0 = inp.v1 ∧ st.regs 1 = nodesAddr ∧ st.mem = memStart)
      t2BuildIncBody
      (fun o st => ∃ nodesEnd, o = .returned nodesEnd ∧
        nodesAddr ≤ nodesEnd ∧ nodesEnd ≤ nodesAddr + 3 * inp.embVertSum ∧
        ZeroFrom st.mem nodesEnd ∧
        T2BuildIncFrame ctx memStart st.mem ∧
        (∀ ci < K, st.mem (inp.compEdgeBaseAddr mW K + ci) = compEdgeBase ctx.wd ci) ∧
        (∀ ci < K, st.mem (inp.vhatOffsetAddr mW K + ci) = vhatBase ctx.wd ci) ∧
        IncListAt st.mem (inp.vHeadAddr mW K) inp.H'.n ctx.wd.comps inp.embJH nodesAddr nodesEnd)
      (fun _ => 55 * inp.embVertSum + 105 * inp.J.m + 70) := by
  intro mW K nodesAddr st ω ⟨hr0, hr1, hm⟩
  have hAgrStart : ∀ x < inp.v1, st.mem x = mem₀ x := fun x hx => (hm ▸ hAgr0) x hx
  have hst := ctx.agrees_preserves_static hAgrStart
  have hEmbStart := hst.2.2.1
  have hEmbBnd := hst.2.2.2.1
  have hCompsStart := hst.2.2.2.2.2.1
  have hPrepStart := hst.2.2.2.2.1
  have hW : 1 < 2 ^ w := ctx.hww.1
  have hMax : nodesAddr + 3 * inp.embVertSum < 2 ^ w :=
    lt_of_le_of_lt (t2_nodesEnd_le_maxWord ctx) ctx.hww.2.2
  have hchain := t2_prep_chain_bounds ctx
  have hdisj : inp.v1 + 32 ≤ inp.compEdgeBaseAddr mW K ∧
      inp.compEdgeBaseAddr mW K + K = inp.vhatOffsetAddr mW K ∧
      inp.vhatOffsetAddr mW K + K = inp.compEdgeDelRoundAddr mW K ∧
      inp.compEdgeDelRoundAddr mW K ≤ inp.vHeadAddr mW K ∧
      inp.vHeadAddr mW K + inp.H'.n ≤ inp.nodesAddr mW K ∧
      2 * inp.J.m ≤ inp.nodesAddr mW K ∧ inp.H'.n ≤ inp.nodesAddr mW K :=
    t2_v1_le_compEdgeBase ctx
  have hK_le : K ≤ inp.J.m := ctx.hK_le
  have hk_len : K = ctx.wInp.prep.rawComps.length :=
    ctx.wInp.buildCompsFrom_length _ _ _ ctx.hws.1
  suffices hres : ∃ o st' c, Runs w p ω t2BuildIncBody st o st' c ∧
      (∃ nodesEnd, o = .returned nodesEnd ∧
        nodesAddr ≤ nodesEnd ∧ nodesEnd ≤ nodesAddr + 3 * inp.embVertSum ∧
        ZeroFrom st'.mem nodesEnd ∧
        T2BuildIncFrame ctx memStart st'.mem ∧
        (∀ ci < K, st'.mem (inp.compEdgeBaseAddr mW K + ci) = compEdgeBase ctx.wd ci) ∧
        (∀ ci < K, st'.mem (inp.vhatOffsetAddr mW K + ci) = vhatBase ctx.wd ci) ∧
        IncListAt st'.mem (inp.vHeadAddr mW K) inp.H'.n ctx.wd.comps inp.embJH nodesAddr nodesEnd) ∧
      0 + c ≤ 55 * inp.embVertSum + 105 * inp.J.m + 70 by
    simpa only [Nat.zero_add, hm] using hres
  have hst_12 : st.mem (inp.v1 + 12) = inp.embJHAddr := hm ▸ h12
  have hst_13 : st.mem (inp.v1 + 13) = ctx.wInp.prep.h := hm ▸ h13
  have hst_16 : st.mem (inp.v1 + 16) = inp.compEdgeBaseAddr mW K := hm ▸ h16
  have hst_17 : st.mem (inp.v1 + 17) = inp.vhatOffsetAddr mW K := hm ▸ h17
  have hst_20 : st.mem (inp.v1 + 20) = inp.vHeadAddr mW K := hm ▸ h20
  unfold t2BuildIncBody
  refine runs_seq_assign_le (v := ctx.wInp.prep.h)
    (ev_load (ev_add (ev_reg hr0 (by omega)) (ev_const (w := w) (by omega)) (by omega)) hst_13 (by omega)) ?_
  set r2 := Function.update st.regs 2 ctx.wInp.prep.h
  refine runs_seq_assign_le (v := K)
    (ev_load (ev_add (ev_reg (r := 2) (by simp [r2]) (by omega)) (ev_const (w := w) (by omega)) (by omega))
      (hk_len ▸ hPrepStart.2.2.2.1) (by omega)) ?_
  set r3 := Function.update r2 3 K
  refine runs_seq_assign_le (v := ctx.wInp.prep.aComps)
    (ev_load (ev_add (ev_reg (r := 2) (by simp [r3, r2]) (by omega)) (ev_const (w := w) (by omega))
      (by omega)) hPrepStart.2.2.2.2.1 (by omega)) ?_
  set r4 := Function.update r3 4 ctx.wInp.prep.aComps
  refine runs_seq_assign_le (v := inp.compEdgeBaseAddr mW K)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r4, r3, r2, hr0]) (by omega)) (ev_const (w := w) (by omega))
      (by omega)) hst_16 (by omega)) ?_
  set r5 := Function.update r4 5 (inp.compEdgeBaseAddr mW K)
  refine runs_seq_assign_le (v := inp.vhatOffsetAddr mW K)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r5, r4, r3, r2, hr0]) (by omega)) (ev_const (w := w) (by omega))
      (by omega)) hst_17 (by omega)) ?_
  set r6 := Function.update r5 6 (inp.vhatOffsetAddr mW K)
  refine runs_seq_assign_le (v := inp.embJHAddr)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r6, r5, r4, r3, r2, hr0]) (by omega)) (ev_const (w := w) (by omega))
      (by omega)) hst_12 (by have := hEmbBnd.1; omega)) ?_
  set r7 := Function.update r6 7 inp.embJHAddr
  refine runs_seq_assign_le (v := inp.vHeadAddr mW K)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r7, r6, r5, r4, r3, r2, hr0]) (by omega))
      (ev_const (w := w) (by omega)) (by omega)) hst_20 (by omega)) ?_
  set r8 := Function.update r7 8 (inp.vHeadAddr mW K)
  refine runs_seq_assign_le (v := 0) (ev_const (Nat.zero_lt_of_lt hW)) ?_
  set r9 := Function.update r8 9 0
  refine runs_seq_assign_le (v := 0) (ev_const (Nat.zero_lt_of_lt hW)) ?_
  set r10 := Function.update r9 10 0
  refine runs_seq_assign_le (v := nodesAddr) (ev_reg (r := 1) (by simp [r10, r9, r8, r7, r6, r5, r4, r3, r2, hr1]) (by omega)) ?_
  set r11 := Function.update r10 11 nodesAddr
  let scOuter := fun ci => (∑ b ∈ Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m,
    ((inp.embJH ((ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts.length * 49 + 32)) + 54
  let InvO := fun ci (s : State) => T2IncInv ctx memStart ci ci 0 0 s ∧ s.regs 12 = ci
  have hloop := Triple.forRange_le (p := p) (P := fun st_ => st_ = { st with regs := r11 })
    (Inv := InvO) scOuter 0 K (Nat.zero_le _) hW (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨ev_const (Nat.zero_lt_of_lt hW), ⟨by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, hr0],
        by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, r2], by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, K],
        by simp [r11, r10, r9, r8, r7, r6, r5, r4], by simp [r11, r10, r9, r8, r7, r6, r5, mW, K],
        by simp [r11, r10, r9, r8, r7, r6, mW, K], by simp [r11, r10, r9, r8, r7],
        by simp [r11, r10, r9, r8, mW, K],
        by simp [r11, r10, r9, compEdgeBase], by simp [r11, r10, vhatBase],
        by simp [r11, nodesAddr, mW, K],
        by simp only [r11, t2PrefixVerts, Finset.range_zero, Finset.sum_empty, add_zero, mul_zero]; exact Nat.le_refl _,
        fun a ha => by
          rw [hm]; exact hzf0 a (by
            have : inp.nodesAddr mW K ≤ a := by simpa [r11, nodesAddr] using ha
            rcases hdisj with ⟨d1, d2, d3, d4, d5, _⟩; omega),
        fun _ _ => by rw [hm], fun c hc => False.elim (Nat.not_lt_zero _ hc),
        fun c hc => False.elim (Nat.not_lt_zero _ hc), ?_⟩, rfl⟩
      rw [hm]; dsimp only; rw [show Function.update r11 12 0 11 = nodesAddr by simp [r11]]
      exact incListForPairs_mono
        (incListForPairs_init (mem := memStart)
          (comps := ctx.wd.comps) (embJH := inp.embJH) (nH := inp.H'.n)
          (nodesAddr := nodesAddr) (vHeadAddr := inp.vHeadAddr mW K)
          fun x _ => hzf0 _ (by rcases hdisj with ⟨d1, d2, d3, d4, _⟩; omega))
        (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ h => by simp [t2DonePred] at h))
    (fun ci s _ _ h => h.2) (fun ci s _ _ h => ev_reg h.1.2.2.1 (by omega))
    (fun ci _ hci => (t2BuildInc_outer_step ctx hci (hm ▸ hEmbStart) (hm ▸ hEmbBnd)
      (hm ▸ hCompsStart) hW hMax).conseq
      (fun s hs => by simpa [hm] using hs)
      (fun o s ho => by
        cases o with
        | returned _ => exact False.elim ho
        | normal => exact ⟨⟨ho.1, by simp⟩, ho.2⟩)
      (fun _ _ => by dsimp only [scOuter]; rw [List.getD_eq_getElem _ _ hci]))
  refine runs_seq_triple_le (Q₁ := InvO K) hloop rfl fun st₁ hq₁ => ?_
  rcases hq₁ with ⟨⟨_, _, _, _, _, _, _, _, _, _, hlo, hhi, hzf', hfr', hceb', hvho', hInc'⟩, _⟩
  set nodesEnd := st₁.regs 11
  have hhend_le : nodesEnd ≤ nodesAddr + 3 * inp.embVertSum :=
    le_trans hhi (Nat.add_le_add_left (Nat.mul_le_mul_left 3 (t2PrefixVerts_le_embVertSum ctx (le_refl _))) _)
  have h_incAt : IncListAt st₁.mem (inp.vHeadAddr mW K) inp.H'.n ctx.wd.comps inp.embJH nodesAddr nodesEnd :=
    incListForPairs_to_incListAt (incListForPairs_mono hInc' (fun _ _ => rfl) (fun _ _ _ => rfl)
      fun ci' b' x' ⟨hci', hb', hmem⟩ => by
        dsimp only [t2DonePred]
        rw [List.getD_eq_getElem _ _ hci']
        exact Or.inl ⟨hci', hb', hmem⟩)
  have hsum_vert := t2_inc_vertSum_le_ctx ctx
  have hsum_j : ∑ ci ∈ Finset.range K, (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m ≤ inp.J.m := by
    have hs : (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m := by
      have h := mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
      change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ ctx.wInp.prep.J.m at h
      rw [ctx.hWInpJ] at h; omega
    dsimp only [K]; rwa [← sum_range_getD_nat ctx.wd.comps defaultCompInfo (fun c => c.J_sub.m)] at hs
  have hrc_bound : rangeCost scOuter 0 K + K * 9 + 7 ≤ 49 * inp.embVertSum + 95 * inp.J.m + 7 := by
    rw [rangeCost_zero_eq_sum]
    have heq : (∑ ci ∈ Finset.range K, scOuter ci) + K * 9 + 7 =
        49 * (∑ ci ∈ Finset.range K,
          ∑ b ∈ Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m,
            (inp.embJH ((ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts.length) +
          32 * (∑ ci ∈ Finset.range K, (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m) + 63 * K + 7 := by
      simp only [scOuter, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        ← Finset.sum_mul]
      ring
    rw [heq]; dsimp only [K] at hsum_j hK_le heq ⊢; omega
  exact runs_ret_le (ev_reg (r := 11) rfl (by omega))
    ⟨nodesEnd, rfl, hlo, hhend_le, hzf', hfr', hceb', hvho', h_incAt⟩
    (by simp only [Expr.size]; omega)

end MinCostFlow.Spanner
