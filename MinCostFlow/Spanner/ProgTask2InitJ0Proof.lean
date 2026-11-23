module

public import MinCostFlow.Spanner.ProgTask2InitJ0

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Outer loop and end-to-end triple for `t2InitJ0Body` -/

private lemma t2InitJ0_outer_step {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T2Ctx impl inp mem₀ w) {memStart : ℕ → ℕ}
    {arena0 eW : ℕ} (heW : eW < ctx.wd.j0Edges.length)
    (hJ_at : GraphAt memStart inp.jAddr inp.J)
    (hEmb : EmbAt memStart inp.embJHAddr inp.J.m inp.embJH)
    (hEmbBnd : EmbBounded memStart inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr)
    (hPrep : PrepStaticState ctx.wInp.prep memStart memStart)
    (hStat : ctx.StaticOutAt memStart)
    (hj_t1 : inp.jAddr + inp.J.encode.length ≤ inp.t1OutAddr)
    (har_lo : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ arena0)
    (har_hi : arena0 ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum)
    (hVcongBnd : ∀ e < ctx.wd.j0Edges.length, ∀ x < inp.H'.n,
      j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH e x +
        memStart (memStart (ctx.wInp.h + 14) + e) < 2 ^ w) :
    let vertsLen := (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.length
    Triple w p
      (fun st => T2InitJ0OuterInv ctx memStart arena0 eW st ∧ st.regs 13 = eW)
      (Stmt.assign 14 (t2Ld (.reg 5) (.reg 13)) ;;
       Stmt.assign 15 (t2Ld (.reg 1) (t2Add (.const 2) (t2Mul (.const 2) (.reg 14)))) ;;
       Stmt.assign 16 (t2Ld (.reg 1) (t2Add (.const 3) (t2Mul (.const 2) (.reg 14)))) ;;
       Stmt.store (.reg 12) (.const 2) ;;
       t2St (.reg 12) (.const 1) (.reg 15) ;;
       t2St (.reg 12) (.const 2) (.reg 16) ;;
       t2St (.reg 12) (.const 3) (.const 1) ;;
       t2St (.reg 12) (.const 4) (.reg 14) ;;
       t2St (.reg 6) (.reg 13) (.reg 12) ;;
       Stmt.assign 12 (t2Add (.reg 12) (.const 5)) ;;
       Stmt.assign 17 (t2Add (.reg 13) (.const 1)) ;;
       Stmt.assign 18 (t2Ld (.reg 8) (.reg 13)) ;;
       Stmt.assign 19 (t2Ld (.reg 9) (.reg 14)) ;;
       Stmt.assign 20 (.load (.reg 19)) ;;
       forRange 21 (.const 0) (.reg 20) (
         Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
         Stmt.cond (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)) (
           t2St (.reg 11) (.reg 22) (.reg 17) ;;
           t2St (.reg 10) (.reg 22) (t2Add (t2Ld (.reg 10) (.reg 22)) (.reg 18))
         ) Stmt.nop
       ))
      (normalPost fun st₁ =>
        T2InitJ0OuterInv ctx memStart arena0 (eW + 1)
          { st₁ with regs := Function.update st₁.regs 13 (eW + 1) } ∧ st₁.regs 13 = eW)
      (fun _ => 45 * vertsLen + 101) := by
  intro vertsLen st ω ⟨hinv, hr13⟩
  rcases hinv with ⟨hr0, hr1, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12,
    hzf, hfr, hEmbWJ, hVcong, hStamp⟩
  dsimp only [vertsLen] at ⊢
  set mW := ctx.wd.W.m
  set K := ctx.wd.comps.length
  set jOrig := ctx.wd.j0Edges.getD eW 0
  set walk := inp.embJH jOrig
  set wWNum := fun i => memStart (memStart (ctx.wInp.h + 14) + i)
  have hbnd := t2_initJ0_bounds ctx har_lo har_hi
  have b1 : inp.v1 + 32 = inp.embWJAddr := hbnd.1
  have b2 : inp.embWJAddr + mW = inp.dsHandlesAddr mW := hbnd.2.1
  have b3 : inp.dsHandlesAddr mW + K = inp.compEdgeBaseAddr mW K := hbnd.2.2.1
  have b4 : inp.compEdgeBaseAddr mW K + 2 * K = inp.compEdgeDelRoundAddr mW K := hbnd.2.2.2.1
  have b5 : inp.compEdgeDelRoundAddr mW K ≤ inp.vHeadAddr mW K := hbnd.2.2.2.2.1
  have b6 : inp.vHeadAddr mW K + inp.H'.n = inp.vcongNumAddr mW K := hbnd.2.2.2.2.2.1
  have b7 : inp.vcongNumAddr mW K + inp.H'.n = inp.procStampAddr mW K := hbnd.2.2.2.2.2.2.1
  have b8 : inp.procStampAddr mW K + inp.H'.n = inp.eWVertStampAddr mW K := hbnd.2.2.2.2.2.2.2.1
  have b9 : inp.eWVertStampAddr mW K + inp.H'.n = inp.queueAddr mW K := hbnd.2.2.2.2.2.2.2.2.1
  have b10 : inp.queueAddr mW K + inp.H'.n = inp.nodesAddr mW K := hbnd.2.2.2.2.2.2.2.2.2.1
  have hmW : ctx.wd.j0Edges.length ≤ mW := hbnd.2.2.2.2.2.2.2.2.2.2.1
  have har_w : arena0 + 5 * ctx.wd.j0Edges.length < 2 ^ w := hbnd.2.2.2.2.2.2.2.2.2.2.2
  dsimp only [mW, K, jOrig, walk, wWNum] at hr0 hr1 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12 hzf hfr hEmbWJ hVcong hStamp
  dsimp only [mW, K, jOrig, walk, wWNum] at hVcongBnd har_lo har_hi b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 hmW har_w ⊢
  rcases t2_prep_chain_bounds ctx with ⟨hc1, hc2, hc3, hc4⟩
  have hW : 1 < 2 ^ w := ctx.hww.1
  have hjOrig_m : jOrig < inp.J.m := by
    have := ctx.hw_okW.j0_lt jOrig (by dsimp only [jOrig]; rw [List.getD_eq_getElem _ _ heW]; exact List.getElem_mem heW)
    simpa [ctx.hWInpJ] using this
  have hemb_at := hEmb jOrig hjOrig_m
  have hemb_bnd := hEmbBnd.2 jOrig hjOrig_m
  have hj0_eq : ctx.wInp.prep.j0Edges = ctx.wd.j0Edges := rfl
  have hfr_stat : ∀ a < inp.v1, st.mem a = memStart a := fun a ha =>
    hfr a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)
  have hj0_len_w : ctx.wd.j0Edges.length < 2 ^ w := by omega
  have h_emb_lt_ar : inp.embWJAddr + eW + 1 ≤ arena0 := by omega
  have h_vc_lt_ar : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n ≤ arena0 := by omega
  have h_st_lt_ar : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n ≤ arena0 := by omega
  have haJ0_eq : ctx.wInp.prep.aComps = ctx.wInp.prep.aJ0Out + ctx.wInp.prep.j0Edges.length := rfl
  have heW_prep : eW < ctx.wInp.prep.j0Edges.length := by rwa [hj0_eq]
  have haJ0_lt_v1 : ctx.wInp.prep.aJ0Out + eW < inp.v1 := by omega
  have hjOrig_val : st.mem (ctx.wInp.prep.aJ0Out + eW) = jOrig := by
    rw [hfr_stat _ haJ0_lt_v1]
    have hmem := listAt_getElem hPrep.2.2.2.2.2.2.2.2.2.1 heW_prep
    have hmem' : memStart (ctx.wInp.prep.aJ0Out + eW) = ctx.wd.j0Edges[eW] := hmem
    rw [hmem']
    exact (List.getD_eq_getElem _ _ heW).symm
  have hj_len := graph_encode_length inp.J
  have hnJ_le : inp.J.n ≤ inp.v1 := by
    have hdec := ctx.hstat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have := ctx.hw_j0Addr; have := ctx.hw_nlAddr; have := ctx.hw_decAddr
    omega
  have hJ_u : st.mem (inp.jAddr + (2 + 2 * jOrig)) = (inp.J.edges[jOrig]).1 := by
    rw [hfr_stat _ (by omega)]
    simpa only [Nat.add_assoc] using graphAt_edge_fst hJ_at hjOrig_m
  have hJ_v : st.mem (inp.jAddr + (3 + 2 * jOrig)) = (inp.J.edges[jOrig]).2 := by
    rw [hfr_stat _ (by omega)]
    simpa only [Nat.add_assoc] using graphAt_edge_snd hJ_at hjOrig_m
  have hu_lt : (inp.J.edges[jOrig]).1 < 2 ^ w := by
    have := (ctx.hJ (inp.J.edges[jOrig]) (List.getElem_mem hjOrig_m)).1
    omega
  have hv_lt : (inp.J.edges[jOrig]).2 < 2 ^ w := by
    have := (ctx.hJ (inp.J.edges[jOrig]) (List.getElem_mem hjOrig_m)).2
    omega
  have hwW_v1 : memStart (ctx.wInp.h + 14) + eW < inp.v1 := by
    have := hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  have hwWNum_val : st.mem (memStart (ctx.wInp.h + 14) + eW) = wWNum eW :=
    hfr_stat _ hwW_v1
  have hwWNum_w : wWNum eW < 2 ^ w := by
    have hvc := hVcongBnd eW heW
    dsimp only [wWNum] at hvc ⊢
    by_cases hn : 0 < inp.H'.n
    · have := hvc 0 hn; omega
    · have hj0p : 0 < ctx.wd.j0Edges.length := by omega
      have hwb := t2_j0WNum_bound ctx hStat hj0p
      have : memStart (memStart (ctx.wInp.h + 14) + eW) ≤
          ctx.wd.j0Edges.length * Task1Input.phiDenCap impl inp.J := by
        calc memStart (memStart (ctx.wInp.h + 14) + eW)
            ≤ Task1Input.phiDenCap impl inp.J := hwb.1 eW heW
          _ = 1 * Task1Input.phiDenCap impl inp.J := (Nat.one_mul _).symm
          _ ≤ ctx.wd.j0Edges.length * Task1Input.phiDenCap impl inp.J :=
              Nat.mul_le_mul_right _ hj0p
      exact lt_of_le_of_lt this hwb.2
  have hembJH_v1 : inp.embJHAddr + jOrig < inp.v1 := by
    have := hEmbBnd.1
    omega
  have hwalkPtr_val : st.mem (inp.embJHAddr + jOrig) = memStart (inp.embJHAddr + jOrig) :=
    hfr_stat _ hembJH_v1
  have hemb_len : memStart (inp.embJHAddr + jOrig) +
      (2 + walk.verts.length + walk.edges.length) ≤ inp.t1OutAddr := by
    simpa [walk_encode_length, walk, jOrig] using hemb_bnd
  have hwalkLen_val : st.mem (memStart (inp.embJHAddr + jOrig)) = vertsLen := by
    rw [hfr_stat _ (by omega)]
    exact (walkAt_iff.mp hemb_at).1
  have hwalkLen_w : vertsLen < 2 ^ w := by
    dsimp only [vertsLen]
    dsimp only [walk] at hemb_len
    dsimp only [jOrig] at hemb_len ⊢
    omega
  set ptr := arena0 + 5 * eW
  suffices hres : ∃ o st' c, Runs w p ω
      (Stmt.assign 14 (t2Ld (.reg 5) (.reg 13)) ;;
       Stmt.assign 15 (t2Ld (.reg 1) (t2Add (.const 2) (t2Mul (.const 2) (.reg 14)))) ;;
       Stmt.assign 16 (t2Ld (.reg 1) (t2Add (.const 3) (t2Mul (.const 2) (.reg 14)))) ;;
       Stmt.store (.reg 12) (.const 2) ;;
       t2St (.reg 12) (.const 1) (.reg 15) ;;
       t2St (.reg 12) (.const 2) (.reg 16) ;;
       t2St (.reg 12) (.const 3) (.const 1) ;;
       t2St (.reg 12) (.const 4) (.reg 14) ;;
       t2St (.reg 6) (.reg 13) (.reg 12) ;;
       Stmt.assign 12 (t2Add (.reg 12) (.const 5)) ;;
       Stmt.assign 17 (t2Add (.reg 13) (.const 1)) ;;
       Stmt.assign 18 (t2Ld (.reg 8) (.reg 13)) ;;
       Stmt.assign 19 (t2Ld (.reg 9) (.reg 14)) ;;
       Stmt.assign 20 (.load (.reg 19)) ;;
       forRange 21 (.const 0) (.reg 20) (
         Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
         Stmt.cond (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)) (
           t2St (.reg 11) (.reg 22) (.reg 17) ;;
           t2St (.reg 10) (.reg 22) (t2Add (t2Ld (.reg 10) (.reg 22)) (.reg 18))
         ) Stmt.nop
       )) st o st' c ∧
      (normalPost fun st₁ =>
        T2InitJ0OuterInv ctx memStart arena0 (eW + 1)
          { st₁ with regs := Function.update st₁.regs 13 (eW + 1) } ∧ st₁.regs 13 = eW) o st' ∧
      0 + c ≤ 45 * vertsLen + 101 by
    simpa only [Nat.zero_add] using hres
  refine runs_seq_assign_le (v := jOrig)
    (ev_load (ev_add (ev_reg hr5 (by omega)) (ev_reg hr13 (by omega)) (by omega)) hjOrig_val (by omega)) ?_
  set r14 := Function.update st.regs 14 jOrig
  refine runs_seq_assign_le (v := (inp.J.edges[jOrig]).1)
    (ev_load (ev_add (ev_reg (r := 1) (by simp [r14, hr1]) (by omega))
      (ev_add (ev_const (w := w) (by omega)) (ev_mul (ev_const (w := w) (by omega))
        (ev_reg (r := 14) (by simp [r14]) (by omega)) (by omega)) (by omega)) (by omega))
      hJ_u hu_lt) ?_
  set u := (inp.J.edges[jOrig]).1
  set r15 := Function.update r14 15 u
  refine runs_seq_assign_le (v := (inp.J.edges[jOrig]).2)
    (ev_load (ev_add (ev_reg (r := 1) (by simp [r15, r14, hr1]) (by omega))
      (ev_add (ev_const (w := w) (by omega)) (ev_mul (ev_const (w := w) (by omega))
        (ev_reg (r := 14) (by simp [r15, r14]) (by omega)) (by omega)) (by omega)) (by omega))
      hJ_v hv_lt) ?_
  set v := (inp.J.edges[jOrig]).2
  set r16 := Function.update r15 16 v
  refine runs_seq_store_le (ev_reg (r := 12) (v := ptr) (by simp [r16, r15, r14, hr12]) (by omega))
    (ev_const (w := w) (by omega)) ?_
  set m1 := Function.update st.mem ptr 2
  refine runs_seq_store_le (ev_add (ev_reg (r := 12) (v := ptr) (by simp [r16, r15, r14, hr12]) (by omega))
    (ev_const (w := w) hW) (by omega)) (ev_reg (r := 15) (v := u) (by simp [r16, r15]) hu_lt) ?_
  set m2 := Function.update m1 (ptr + 1) u
  refine runs_seq_store_le (ev_add (ev_reg (r := 12) (v := ptr) (by simp [r16, r15, r14, hr12]) (by omega))
    (ev_const (w := w) (by omega)) (by omega)) (ev_reg (r := 16) (v := v) (by simp [r16]) hv_lt) ?_
  set m3 := Function.update m2 (ptr + 2) v
  refine runs_seq_store_le (ev_add (ev_reg (r := 12) (v := ptr) (by simp [r16, r15, r14, hr12]) (by omega))
    (ev_const (w := w) (by omega)) (by omega)) (ev_const (w := w) hW) ?_
  set m4 := Function.update m3 (ptr + 3) 1
  refine runs_seq_store_le (ev_add (ev_reg (r := 12) (v := ptr) (by simp [r16, r15, r14, hr12]) (by omega))
    (ev_const (w := w) (by omega)) (by omega)) (ev_reg (r := 14) (v := jOrig) (by simp [r16, r15, r14]) (by omega)) ?_
  set m5 := Function.update m4 (ptr + 4) jOrig
  refine runs_seq_store_le (ev_add (ev_reg (r := 6) (v := inp.embWJAddr) (by simp [r16, r15, r14, hr6]) (by omega))
    (ev_reg (r := 13) (v := eW) (by simp [r16, r15, r14, hr13]) (by omega)) (by omega))
    (ev_reg (r := 12) (v := ptr) (by simp [r16, r15, r14, hr12]) (by omega)) ?_
  set m6 := Function.update m5 (inp.embWJAddr + eW) ptr
  have hm6_ne : ∀ a, a ≠ inp.embWJAddr + eW → (a < ptr ∨ ptr + 5 ≤ a) → m6 a = st.mem a :=
    fun a h1 h2 => by
      dsimp only [m6, m5, m4, m3, m2, m1]
      rw [Function.update_of_ne h1, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hptr5 : ptr + 5 = arena0 + 5 * (eW + 1) := by dsimp only [ptr]; omega
  refine runs_seq_assign_le (v := ptr + 5)
    (ev_add (ev_reg (r := 12) (v := ptr) (by simp [r16, r15, r14, hr12]) (by omega))
      (ev_const (w := w) (by omega)) (by dsimp only [ptr]; omega)) ?_
  rw [hptr5]
  set r12' := Function.update r16 12 (arena0 + 5 * (eW + 1))
  refine runs_seq_assign_le (v := eW + 1)
    (ev_add (ev_reg (r := 13) (by simp [r12', r16, r15, r14, hr13]) (by omega))
      (ev_const (w := w) hW) (by omega)) ?_
  set r17 := Function.update r12' 17 (eW + 1)
  have hm6_wnum : m6 (memStart (ctx.wInp.h + 14) + eW) = wWNum eW := by
    rw [hm6_ne _ (by omega) (Or.inl (by dsimp only [ptr]; omega))]
    exact hwWNum_val
  refine runs_seq_assign_le (v := wWNum eW)
    (ev_load (ev_add (ev_reg (r := 8) (by simp [r17, r12', r16, r15, r14, hr8]) (by omega))
      (ev_reg (r := 13) (by simp [r17, r12', r16, r15, r14, hr13]) (by omega)) (by omega))
      hm6_wnum hwWNum_w) ?_
  set r18 := Function.update r17 18 (wWNum eW)
  have hm6_wptr : m6 (inp.embJHAddr + jOrig) = memStart (inp.embJHAddr + jOrig) := by
    rw [hm6_ne _ (by omega) (Or.inl (by dsimp only [ptr]; omega))]
    exact hwalkPtr_val
  refine runs_seq_assign_le (v := memStart (inp.embJHAddr + jOrig))
    (ev_load (ev_add (ev_reg (r := 9) (by simp [r18, r17, r12', r16, r15, r14, hr9]) (by omega))
      (ev_reg (r := 14) (by simp [r18, r17, r12', r16, r15, r14]) (by omega)) (by omega))
      hm6_wptr (by have := hEmbBnd.1; omega)) ?_
  set r19 := Function.update r18 19 (memStart (inp.embJHAddr + jOrig))
  have hm6_wlen : m6 (memStart (inp.embJHAddr + jOrig)) = vertsLen := by
    rw [hm6_ne _ (by omega) (Or.inl (by dsimp only [ptr]; omega))]
    exact hwalkLen_val
  refine runs_seq_assign_le (v := vertsLen)
    (ev_load (ev_reg (r := 19) (by simp [r19]) (by have := hEmbBnd.1; omega)) hm6_wlen hwalkLen_w) ?_
  set r20 := Function.update r19 20 vertsLen
  have hm6_zf : ZeroFrom m6 (arena0 + 5 * (eW + 1)) := fun a ha => by
    rw [hm6_ne a (by omega) (Or.inr (by dsimp only [ptr]; omega))]
    exact hzf a (by omega)
  have hm6_fr : T2InitJ0Frame inp mW K arena0 memStart m6 :=
    t2InitJ0Frame_upd_embWJ (t2InitJ0Frame_upd_arena (t2InitJ0Frame_upd_arena
      (t2InitJ0Frame_upd_arena (t2InitJ0Frame_upd_arena (t2InitJ0Frame_upd_arena hfr
        (by omega)) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)
  have hm6_emb : InitJ0EmbUpTo m6 inp.embWJAddr arena0 (eW + 1) mW inp.J ctx.wd.j0Edges := by
    intro i hi
    refine ⟨fun hi1 => ?_, fun hi1 => ?_⟩
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi1) with hlt | rfl
      · have hpi := (hEmbWJ i hi).1 hlt
        refine ⟨(hm6_ne (inp.embWJAddr + i) (by omega) (Or.inl (by dsimp only [ptr]; omega))).trans hpi.1, ?_⟩
        have hm5_eq : ∀ q, q < ptr ∨ ptr + 5 ≤ q → m5 q = st.mem q := fun q hq => by
          dsimp only [m5, m4, m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        have hw5 := walkAt_of_agreeOutside (lo := ptr) (hi := ptr + 5) hpi.2 hm5_eq
          (Or.inl (by simp only [t2J0Walk, List.length_cons, List.length_nil]; dsimp only [ptr]; omega))
        exact walkAt_of_agreeOutside (lo := inp.embWJAddr + eW) (hi := inp.embWJAddr + eW + 1) hw5
          (fun q hq => by dsimp only [m6]; rw [Function.update_of_ne (by rcases hq with h | h <;> omega)])
          (Or.inr (Nat.le_trans h_emb_lt_ar (Nat.le_add_right _ _)))
      · have hm6_ptr : m6 (inp.embWJAddr + i) = ptr := Function.update_self _ _ _
        refine ⟨hm6_ptr, ?_⟩
        refine t2J0Walk_at hjOrig_m (ptr := ptr) (u := u) (v := v) rfl rfl ?_ ?_ ?_ ?_ ?_
        · dsimp only [m6, m5, m4, m3, m2, m1]
          rw [Function.update_of_ne (by dsimp only [ptr]; omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact Function.update_self _ _ _
        · dsimp only [m6, m5, m4, m3, m2]
          rw [Function.update_of_ne (by dsimp only [ptr]; omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact Function.update_self _ _ _
        · dsimp only [m6, m5, m4, m3]
          rw [Function.update_of_ne (by dsimp only [ptr]; omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact Function.update_self _ _ _
        · dsimp only [m6, m5, m4]
          rw [Function.update_of_ne (by dsimp only [ptr]; omega), Function.update_of_ne (by omega)]
          exact Function.update_self _ _ _
        · dsimp only [m6, m5]
          rw [Function.update_of_ne (by dsimp only [ptr]; omega)]
          exact Function.update_self _ _ _
    · rw [hm6_ne (inp.embWJAddr + i) (by omega) (Or.inl (by dsimp only [ptr]; omega))]
      exact (hEmbWJ i hi).2 (by omega)
  let vcongBase := fun x => j0VcongUpTo ctx.wd wWNum inp.embJH eW x
  let InvI := fun j (s : State) =>
    T2InitJ0InnerInv ctx memStart arena0 eW vcongBase j walk s ∧ s.regs 21 = j
  let scInner := fun (_ : ℕ) => 36
  have hloop := Triple.forRange_le (p := p) (P := fun st_ => st_ = { st with regs := r20, mem := m6 })
    (Inv := InvI) scInner 0 vertsLen (Nat.zero_le _) hW (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨ev_const (Nat.zero_lt_of_lt hW), ⟨by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr0],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr1],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr3],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr4],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr5],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr6],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr7],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr8],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr9],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr10],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr11],
        by simp [r20, r19, r18, r17, r12'], by simp [r20, r19, r18, r17, r12', r16, r15, r14, hr13],
        by simp [r20, r19, r18, r17, r12', r16, r15, r14, jOrig],
        by simp [r20, r19, r18, r17], by simp [r20, r19, r18, wWNum],
        by simp [r20, r19, jOrig], by simp [r20, vertsLen, walk, jOrig],
        hm6_zf, hm6_fr, hm6_emb, ?_, ?_⟩, by simp⟩
      · intro x hx
        simp only [List.take_zero, List.not_mem_nil, ↓reduceIte, add_zero, vcongBase]
        rw [hm6_ne (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x)
          (by omega) (Or.inl (by dsimp only [ptr]; omega))]
        exact hVcong x hx
      · intro x hx
        simp only [List.take_zero, List.not_mem_nil, iff_false]
        rw [hm6_ne (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x)
          (by omega) (Or.inl (by dsimp only [ptr]; omega))]
        have hstx := hStamp x hx
        exact ⟨Nat.le_succ_of_le hstx, by omega⟩)
    (fun _ s _ _ h => h.2) (fun _ s _ _ h => ev_reg h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by dsimp only [vertsLen]; omega))
    (fun j _ hj => (t2InitJ0_inner_step ctx heW hj hEmb hEmbBnd har_lo har_hi (hVcongBnd eW heW)).conseq
      (fun _ hs => hs)
      (fun o s ho => by
        cases o with
        | returned _ => exact False.elim ho
        | normal => exact ⟨⟨ho.1, by simp⟩, ho.2⟩)
      (fun _ _ => le_refl _))
  obtain ⟨o, st₁, c_loop, hr_loop, hq_loop, hc_loop⟩ := hloop { st with regs := r20, mem := m6 } ω rfl
  cases o with
  | returned _ => exact False.elim hq_loop
  | normal =>
    rcases hq_loop with ⟨⟨o0, o1, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, _, _, _, _, _,
      ozf, ofr, oEmb, oVcong, oStamp⟩, _⟩
    have hrc : rangeCost scInner 0 vertsLen = vertsLen * 36 := by
      rw [rangeCost_zero_eq_sum]; simp [scInner]
    simp only [Expr.size] at hc_loop ⊢
    have : c_loop ≤ 45 * vertsLen + 101 := by rw [hrc] at hc_loop; omega
    refine ⟨.normal, st₁, c_loop, hr_loop, ?_, by omega⟩
    refine ⟨⟨by simp [o0], by simp [o1], by simp [o3], by simp [o4], by simp [o5], by simp [o6],
      by simp [o7], by simp [o8], by simp [o9], by simp [o10], by simp [o11], by simp [o12],
      ozf, ofr, oEmb, ?_, ?_⟩, o13⟩
    · intro x hx
      rw [oVcong x hx, List.take_length]
      simp [j0VcongUpTo, Finset.sum_range_succ, vcongBase, wWNum]
    · intro x hx
      exact (oStamp x hx).1

theorem t2InitJ0_triple {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ memStart : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T2Ctx impl inp mem₀ w) {arena0 : ℕ}
    (hAgr0 : ∀ x < inp.v1, memStart x = mem₀ x)
    (h0 : memStart inp.v1 = inp.embWJAddr)
    (h12 : memStart (inp.v1 + 12) = inp.embJHAddr)
    (h13 : memStart (inp.v1 + 13) = ctx.wInp.prep.h)
    (h14 : memStart (inp.v1 + 14) = ctx.wInp.h)
    (h21 : memStart (inp.v1 + 21) = inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (h23 : memStart (inp.v1 + 23) = inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hj_t1 : inp.jAddr + inp.J.encode.length ≤ inp.t1OutAddr)
    (har_lo : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ arena0)
    (har_hi : arena0 ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum)
    (hzf0 : ZeroFrom memStart arena0)
    (hEmbZero : ∀ eW < ctx.wd.W.m, memStart (inp.embWJAddr + eW) = 0)
    (hVcZero : ∀ x < inp.H'.n, memStart (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) = 0)
    (hStZero : ∀ x < inp.H'.n, memStart (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) = 0) :
    let mW := ctx.wd.W.m
    let K := ctx.wd.comps.length
    let j0Len := ctx.wd.j0Edges.length
    let wWNum := fun i => memStart (memStart (ctx.wInp.h + 14) + i)
    Triple w p
      (fun st => st.regs 0 = inp.v1 ∧ st.regs 1 = inp.jAddr ∧ st.regs 2 = arena0 ∧ st.mem = memStart)
      t2InitJ0Body
      (fun o st => o = .returned (arena0 + 5 * j0Len) ∧
        ZeroFrom st.mem (arena0 + 5 * j0Len) ∧
        T2InitJ0Frame inp mW K arena0 memStart st.mem ∧
        InitJ0EmbUpTo st.mem inp.embWJAddr arena0 j0Len mW inp.J ctx.wd.j0Edges ∧
        (∀ x < inp.H'.n, st.mem (inp.vcongNumAddr mW K + x) = j0VcongUpTo ctx.wd wWNum inp.embJH j0Len x) ∧
        (∀ x < inp.H'.n, st.mem (inp.eWVertStampAddr mW K + x) ≤ j0Len) ∧
        st.mem (inp.v1 + 25) = arena0 + 5 * j0Len ∧
        st.mem (inp.v1 + 26) = j0Len)
      (fun _ => 110 * j0Len + 45 * inp.embVertSum + 80) := by
  intro mW K j0Len wWNum st ω ⟨hr0, hr1, hr2, hm⟩
  have hAgrStart : ∀ x < inp.v1, st.mem x = mem₀ x := fun x hx => (hm ▸ hAgr0) x hx
  have hst := ctx.agrees_preserves_static hAgrStart
  have hJ_at : GraphAt memStart inp.jAddr inp.J := hm ▸ hst.2.1
  have hEmb : EmbAt memStart inp.embJHAddr inp.J.m inp.embJH := hm ▸ hst.2.2.1
  have hEmbBnd : EmbBounded memStart inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr := hm ▸ hst.2.2.2.1
  have hPrep : PrepStaticState ctx.wInp.prep memStart memStart := hm ▸ hst.2.2.2.2.1
  have hStat : ctx.StaticOutAt memStart := hm ▸ hst.2.2.2.2.2.2.2
  have hbnd := t2_initJ0_bounds ctx har_lo har_hi
  have b1 : inp.v1 + 32 = inp.embWJAddr := hbnd.1
  have b2 : inp.embWJAddr + mW = inp.dsHandlesAddr mW := hbnd.2.1
  have b3 : inp.dsHandlesAddr mW + K = inp.compEdgeBaseAddr mW K := hbnd.2.2.1
  have b4 : inp.compEdgeBaseAddr mW K + 2 * K = inp.compEdgeDelRoundAddr mW K := hbnd.2.2.2.1
  have b5 : inp.compEdgeDelRoundAddr mW K ≤ inp.vHeadAddr mW K := hbnd.2.2.2.2.1
  have b6 : inp.vHeadAddr mW K + inp.H'.n = inp.vcongNumAddr mW K := hbnd.2.2.2.2.2.1
  have b7 : inp.vcongNumAddr mW K + inp.H'.n = inp.procStampAddr mW K := hbnd.2.2.2.2.2.2.1
  have b8 : inp.procStampAddr mW K + inp.H'.n = inp.eWVertStampAddr mW K := hbnd.2.2.2.2.2.2.2.1
  have b9 : inp.eWVertStampAddr mW K + inp.H'.n = inp.queueAddr mW K := hbnd.2.2.2.2.2.2.2.2.1
  have b10 : inp.queueAddr mW K + inp.H'.n = inp.nodesAddr mW K := hbnd.2.2.2.2.2.2.2.2.2.1
  have hmW : j0Len ≤ mW := hbnd.2.2.2.2.2.2.2.2.2.2.1
  have har_w : arena0 + 5 * j0Len < 2 ^ w := hbnd.2.2.2.2.2.2.2.2.2.2.2
  have har_lo' : inp.nodesAddr mW K ≤ arena0 := har_lo
  have h_ge_emb : inp.v1 + 27 ≤ inp.embWJAddr := by omega
  have h_ge_vc : inp.v1 + 27 ≤ inp.vcongNumAddr mW K := by omega
  have h_ge_st : inp.v1 + 27 ≤ inp.eWVertStampAddr mW K := by omega
  have h_ge_ar : inp.v1 + 27 ≤ arena0 := by omega
  have hW : 1 < 2 ^ w := ctx.hww.1
  rcases t2_prep_chain_bounds ctx with ⟨hc1, hc2, hc3, hc4⟩
  have hv1_w : inp.v1 < 2 ^ w := by omega
  have haJ0_eq : ctx.wInp.prep.aComps = ctx.wInp.prep.aJ0Out + j0Len := rfl
  have haJ0_w : ctx.wInp.prep.aJ0Out < 2 ^ w := by omega
  have hwH_lt_v1 : ctx.wInp.h + 20 ≤ inp.v1 := by
    have hst1 := hStat.2.2.2.2.2.2.2.2.2.2.2.1
    have hst2 := hStat.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hst3 := hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hst4 := hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  have hembJH_w : inp.embJHAddr < 2 ^ w := by
    have := hEmbBnd.1
    omega
  have hj0_eq : ctx.wInp.prep.j0Edges = ctx.wd.j0Edges := rfl
  have hVcongBnd : ∀ e < j0Len, ∀ x < inp.H'.n,
      j0VcongUpTo ctx.wd wWNum inp.embJH e x + wWNum e < 2 ^ w := by
    intro e he x _
    have hj0_pos : 0 < j0Len := by omega
    have hwb := t2_j0WNum_bound ctx hStat hj0_pos
    have hsum : j0VcongUpTo ctx.wd wWNum inp.embJH e x ≤ e * Task1Input.phiDenCap impl inp.J := by
      unfold j0VcongUpTo
      calc ∑ i ∈ Finset.range e, (if x ∈ (inp.embJH (ctx.wd.j0Edges.getD i 0)).verts then wWNum i else 0)
          ≤ ∑ _i ∈ Finset.range e, Task1Input.phiDenCap impl inp.J := by
            refine Finset.sum_le_sum fun i hi => ?_
            split_ifs
            · exact hwb.1 i (lt_trans (Finset.mem_range.mp hi) he)
            · exact Nat.zero_le _
        _ = e * Task1Input.phiDenCap impl inp.J := by simp
    have he1 : e + 1 ≤ j0Len := he
    have hm1 : (e + 1) * Task1Input.phiDenCap impl inp.J ≤ j0Len * Task1Input.phiDenCap impl inp.J :=
      Nat.mul_le_mul_right _ he1
    have hw_e := hwb.1 e he
    have hm2 : j0VcongUpTo ctx.wd wWNum inp.embJH e x + wWNum e ≤
        (e + 1) * Task1Input.phiDenCap impl inp.J := by
      rw [Nat.succ_mul]; exact Nat.add_le_add hsum hw_e
    exact lt_of_le_of_lt (le_trans hm2 hm1) hwb.2
  suffices hres : ∃ o st' c, Runs w p ω t2InitJ0Body st o st' c ∧
      (o = .returned (arena0 + 5 * j0Len) ∧
        ZeroFrom st'.mem (arena0 + 5 * j0Len) ∧
        T2InitJ0Frame inp mW K arena0 memStart st'.mem ∧
        InitJ0EmbUpTo st'.mem inp.embWJAddr arena0 j0Len mW inp.J ctx.wd.j0Edges ∧
        (∀ x < inp.H'.n, st'.mem (inp.vcongNumAddr mW K + x) = j0VcongUpTo ctx.wd wWNum inp.embJH j0Len x) ∧
        (∀ x < inp.H'.n, st'.mem (inp.eWVertStampAddr mW K + x) ≤ j0Len) ∧
        st'.mem (inp.v1 + 25) = arena0 + 5 * j0Len ∧
        st'.mem (inp.v1 + 26) = j0Len) ∧
      0 + c ≤ 110 * j0Len + 45 * inp.embVertSum + 80 by
    simpa only [Nat.zero_add] using hres
  have hst_13 : st.mem (inp.v1 + 13) = ctx.wInp.prep.h := hm ▸ h13
  have hst_0 : st.mem inp.v1 = inp.embWJAddr := hm ▸ h0
  have hst_14 : st.mem (inp.v1 + 14) = ctx.wInp.h := hm ▸ h14
  have hst_12 : st.mem (inp.v1 + 12) = inp.embJHAddr := hm ▸ h12
  have hst_21 : st.mem (inp.v1 + 21) = inp.vcongNumAddr mW K := hm ▸ h21
  have hst_23 : st.mem (inp.v1 + 23) = inp.eWVertStampAddr mW K := hm ▸ h23
  have hst_j0 : st.mem ctx.wInp.prep.h = j0Len := by rw [hm, hPrep.2.1]; rfl
  have hst_aJ0 : st.mem (ctx.wInp.prep.h + 1) = ctx.wInp.prep.aJ0Out := hm ▸ hPrep.2.2.1
  have hst_wW : st.mem (ctx.wInp.h + 14) = memStart (ctx.wInp.h + 14) := hm ▸ rfl
  have hwW_addr_w : memStart (ctx.wInp.h + 14) < 2 ^ w := by
    have := hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  unfold t2InitJ0Body
  refine runs_seq_assign_le (v := ctx.wInp.prep.h)
    (ev_load (ev_add (ev_reg hr0 (by omega)) (ev_const (w := w) (by omega)) (by omega)) hst_13 (by omega)) ?_
  set r3 := Function.update st.regs 3 ctx.wInp.prep.h
  refine runs_seq_assign_le (v := j0Len)
    (ev_load (ev_reg (r := 3) (by simp [r3]) (by omega)) hst_j0 (by omega)) ?_
  set r4 := Function.update r3 4 j0Len
  refine runs_seq_assign_le (v := ctx.wInp.prep.aJ0Out)
    (ev_load (ev_add (ev_reg (r := 3) (by simp [r4, r3]) (by omega)) (ev_const (w := w) hW) (by omega))
      hst_aJ0 haJ0_w) ?_
  set r5 := Function.update r4 5 ctx.wInp.prep.aJ0Out
  refine runs_seq_assign_le (v := inp.embWJAddr)
    (ev_load (ev_reg (r := 0) (by simp [r5, r4, r3, hr0]) (by omega)) hst_0 (by omega)) ?_
  set r6 := Function.update r5 6 inp.embWJAddr
  refine runs_seq_assign_le (v := ctx.wInp.h)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r6, r5, r4, r3, hr0]) (by omega))
      (ev_const (w := w) (by omega)) (by omega)) hst_14 (by omega)) ?_
  set r7 := Function.update r6 7 ctx.wInp.h
  refine runs_seq_assign_le (v := memStart (ctx.wInp.h + 14))
    (ev_load (ev_add (ev_reg (r := 7) (by simp [r7]) (by omega)) (ev_const (w := w) (by omega)) (by omega))
      hst_wW hwW_addr_w) ?_
  set r8 := Function.update r7 8 (memStart (ctx.wInp.h + 14))
  refine runs_seq_assign_le (v := inp.embJHAddr)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r8, r7, r6, r5, r4, r3, hr0]) (by omega))
      (ev_const (w := w) (by omega)) (by omega)) hst_12 hembJH_w) ?_
  set r9 := Function.update r8 9 inp.embJHAddr
  refine runs_seq_assign_le (v := inp.vcongNumAddr mW K)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r9, r8, r7, r6, r5, r4, r3, hr0]) (by omega))
      (ev_const (w := w) (by omega)) (by omega)) hst_21 (by omega)) ?_
  set r10 := Function.update r9 10 (inp.vcongNumAddr mW K)
  refine runs_seq_assign_le (v := inp.eWVertStampAddr mW K)
    (ev_load (ev_add (ev_reg (r := 0) (by simp [r10, r9, r8, r7, r6, r5, r4, r3, hr0]) (by omega))
      (ev_const (w := w) (by omega)) (by omega)) hst_23 (by omega)) ?_
  set r11 := Function.update r10 11 (inp.eWVertStampAddr mW K)
  refine runs_seq_assign_le (v := arena0)
    (ev_reg (r := 2) (by simp [r11, r10, r9, r8, r7, r6, r5, r4, r3, hr2]) (by omega)) ?_
  set r12 := Function.update r11 12 arena0
  let scOuter := fun eW => 45 * (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.length + 101
  let InvO := fun upTo (s : State) => T2InitJ0OuterInv ctx memStart arena0 upTo s ∧ s.regs 13 = upTo
  have hloop := Triple.forRange_le (p := p) (P := fun st_ => st_ = { st with regs := r12 })
    (Inv := InvO) scOuter 0 j0Len (Nat.zero_le _) hW (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨ev_const (Nat.zero_lt_of_lt hW), ⟨by simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, hr0],
        by simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, hr1],
        by simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3],
        by simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, j0Len],
        by simp [r12, r11, r10, r9, r8, r7, r6, r5],
        by simp [r12, r11, r10, r9, r8, r7, r6],
        by simp [r12, r11, r10, r9, r8, r7],
        by simp [r12, r11, r10, r9, r8],
        by simp [r12, r11, r10, r9],
        by simp [r12, r11, r10, mW, K],
        by simp [r12, r11, mW, K],
        by simp [r12],
        by simpa [hm] using hzf0, by rw [hm]; exact t2InitJ0Frame_refl _ _ _ _ _, ?_, ?_, ?_⟩, rfl⟩
      · intro i hi
        exact ⟨fun h0i => False.elim (Nat.not_lt_zero _ h0i), fun _ => hm ▸ hEmbZero i hi⟩
      · intro x hx
        simp only [j0VcongUpTo, Finset.range_zero, Finset.sum_empty, hm, hVcZero x hx]
      · intro x hx
        simp only [hm, hStZero x hx, Nat.zero_le])
    (fun _ s _ _ h => h.2) (fun _ s _ _ h => ev_reg h.1.2.2.2.1 (by omega))
    (fun eW _ heW => (t2InitJ0_outer_step ctx heW hJ_at hEmb hEmbBnd hPrep hStat hj_t1
      har_lo har_hi hVcongBnd).conseq
      (fun _ hs => hs)
      (fun o s ho => by
        cases o with
        | returned _ => exact False.elim ho
        | normal => exact ⟨⟨ho.1, by simp⟩, ho.2⟩)
      (fun _ _ => le_refl _))
  refine runs_seq_triple_le (Q₁ := InvO j0Len) hloop rfl fun st₁ hq₁ => ?_
  rcases hq₁ with ⟨⟨hr0', _, _, hr4', _, _, _, _, _, _, _, hr12', hzf', hfr', hEmb', hVc', hSt'⟩, _⟩
  refine runs_seq_store_le
    (ev_add (ev_reg hr0' (by omega)) (ev_const (w := w) (by omega)) (by omega))
    (ev_reg hr12' (by omega)) ?_
  set m_25 := Function.update st₁.mem (inp.v1 + 25) (arena0 + 5 * j0Len)
  refine runs_seq_store_le
    (ev_add (ev_reg hr0' (by omega)) (ev_const (w := w) (by omega)) (by omega))
    (ev_reg hr4' (by omega)) ?_
  set m_26 := Function.update m_25 (inp.v1 + 26) j0Len
  have hrc_bound : rangeCost scOuter 0 j0Len + j0Len * 9 + 7 ≤
      110 * j0Len + 45 * inp.embVertSum + 10 := by
    rw [rangeCost_zero_eq_sum]
    have hverts := t2_j0VertSum_le_embVertSum ctx
    dsimp only [j0Len] at hverts ⊢
    simp only [scOuter, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Finset.mul_sum]
    omega
  have hm26_below : ∀ a, inp.v1 + 27 ≤ a → m_26 a = st₁.mem a := fun a ha => by
    dsimp only [m_26, m_25]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hpost :
      ZeroFrom m_26 (arena0 + 5 * j0Len) ∧
      T2InitJ0Frame inp mW K arena0 memStart m_26 ∧
      InitJ0EmbUpTo m_26 inp.embWJAddr arena0 j0Len mW inp.J ctx.wd.j0Edges ∧
      (∀ x < inp.H'.n, m_26 (inp.vcongNumAddr mW K + x) = j0VcongUpTo ctx.wd wWNum inp.embJH j0Len x) ∧
      (∀ x < inp.H'.n, m_26 (inp.eWVertStampAddr mW K + x) ≤ j0Len) ∧
      m_26 (inp.v1 + 25) = arena0 + 5 * j0Len ∧
      m_26 (inp.v1 + 26) = j0Len := by
    refine ⟨?_, t2InitJ0Frame_upd_v26 (t2InitJ0Frame_upd_v25 hfr'), ?_, ?_, ?_, ?_, ?_⟩
    · exact fun a ha => by
        rw [hm26_below a (Nat.le_trans h_ge_ar (Nat.le_trans (Nat.le_add_right _ _) ha))]
        exact hzf' a ha
    · intro eW heW
      have hp := hEmb' eW heW
      have hm_ptr : m_26 (inp.embWJAddr + eW) = st₁.mem (inp.embWJAddr + eW) :=
        hm26_below (inp.embWJAddr + eW) (Nat.le_trans h_ge_emb (Nat.le_add_right _ _))
      refine ⟨fun he => ?_, fun he => hm_ptr.trans (hp.2 he)⟩
      · have hp1 := hp.1 he
        exact ⟨hm_ptr.trans hp1.1, walkAt_of_agreeOutside (lo := 0) (hi := arena0) hp1.2
          (fun a ha => ha.elim (fun h => False.elim (Nat.not_lt_zero _ h))
            (fun h => hm26_below a (Nat.le_trans h_ge_ar h))) (Or.inr (by omega))⟩
    · intro x hx
      rw [hm26_below (inp.vcongNumAddr mW K + x) (Nat.le_trans h_ge_vc (Nat.le_add_right _ _))]
      dsimp only [mW, K, wWNum]
      exact hVc' x hx
    · intro x hx
      rw [hm26_below (inp.eWVertStampAddr mW K + x) (Nat.le_trans h_ge_st (Nat.le_add_right _ _))]
      dsimp only [mW, K]
      exact hSt' x hx
    · dsimp only [m_26, m_25]
      rw [Function.update_of_ne (by omega : inp.v1 + 25 ≠ inp.v1 + 26)]
      exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  refine runs_ret_le (ev_reg hr12' (by omega)) ⟨rfl, by dsimp only; exact hpost⟩
    (by simp only [Expr.size]; omega)

end MinCostFlow.Spanner
