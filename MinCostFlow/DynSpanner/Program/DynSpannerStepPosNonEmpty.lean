module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNERuns

/-!
# The nonempty `E_aff` branch of a `0 < j` step: the contract theorem

Proves `dsStepPosNonEmpty_meetsContract`: `dsStepPosNonEmptyStmt` runs `dsSumWalkLens`,
`dsSparsifyStage`, `dsReembStage`, `dsStepFinish`, `gen++`, `dsCollectD` and the three-word store
at `heapStep`, ends in `StepPosMidPost`, returns a heap pointer at most `dsStepPosNonEmptyEnd`, and
runs within `dsStepPosNonEmptyCost`. The steps after `dsReembStage` are `stepPosNE_tail_run`
(`DynSpannerStepPosNERuns.lean`).
-/

public section

namespace MinCostFlow.DynSpanner.Program

open WordRAM

/-- `dsStepPosNonEmptyStmt` meets `dsStepPosNonEmptyContract`. -/
theorem dsStepPosNonEmpty_meetsContract (ctx : StepPosNECtx) {p : Program} {bs : StepPosNEBases}
    (hp : HasStepPosNEProcs ctx.impl p bs) :
    MeetsContract ctx.w p (bs.bNE + stepPosNonEmptyIdx) (dsStepPosNonEmptyContract ctx) := by
  refine meetsContract_of_runs
    (hp.hpNE.get (i := stepPosNonEmptyIdx) (by simp [stepPosNonEmptyProcs, stepPosNonEmptyIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, rfl⟩
  simp only [stepPosNonEmptyProcs, stepPosNonEmptyIdx, List.getElem_cons_zero]
  dsimp only [dsStepPosNonEmptyStmt]
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hwb := stepPosNE_word_bounds ctx
  have hHdr_aff : ctx.memAff (ctx.b + dsLOff) = ctx.L ∧
      ctx.memAff (ctx.b + dsVCapOff) = ctx.vCap ∧
      ctx.memAff (ctx.b + dsECapOff) = ctx.eCap := by
    have hag : ∀ off, off < dsHdrSize → off ≠ dsGenOff →
        ctx.memAff (ctx.b + off) = ctx.mem0 (ctx.b + off) := fun off ho1 ho2 =>
      (ctx.hAff_frame (ctx.b + off) (by omega) (by omega) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
        (ctx.hHdr_02 (ctx.b + off) (Nat.le_add_right _ _) (by rw [← hfl.1]; omega) (by omega))
    exact ⟨by rw [hag dsLOff (by simp [dsLOff, dsHdrSize]) (by simp [dsLOff, dsGenOff])]
              exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           by rw [hag dsVCapOff (by simp [dsVCapOff, dsHdrSize]) (by simp [dsVCapOff, dsGenOff])]
              exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           by rw [hag dsECapOff (by simp [dsECapOff, dsHdrSize]) (by simp [dsECapOff, dsGenOff])]
              exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have hAuxN : ctx.memAff (dsAuxPtr ctx.b ctx.vCap ctx.eCap + dgNOff) = ctx.J.n :=
    ctx.hAff_aux.2.2.2.2.2.1
  -- Step through the 17 header/layout assigns cleanly in two batches
  refine stepPosNE_runs_cost_start ?_
  refine stepPosNE_hdr_a ctx.hw16 hwb.1 ?_ ?_ ?_ ?_ ?_
  · simp [startState]
  · exact hHdr_aff.1
  · exact hHdr_aff.2.1
  · exact hHdr_aff.2.2
  intro regs0 hR0_lo hR0_hi
  obtain ⟨h0_8, h0_9, h0_10, h0_11, h0_12, h0_13, h0_14, h0_15, h0_16⟩ := hR0_hi
  refine stepPosNE_hdr_b ctx.hw16 hwb.1 h0_8 h0_9 h0_10 h0_16 ?_
  intro regs1 hR1_lo hR1_hi
  have hr0 : regs1 0 = ctx.b := by rw [hR1_lo 0 (by decide)]; exact (hR0_lo 0 (by decide)).trans (by simp [startState])
  have hr1 : regs1 1 = ctx.j := by rw [hR1_lo 1 (by decide)]; exact (hR0_lo 1 (by decide)).trans (by simp [startState])
  have hr2 : regs1 2 = ctx.eAffPtr := by rw [hR1_lo 2 (by decide)]; exact (hR0_lo 2 (by decide)).trans (by simp [startState])
  have hr3 : regs1 3 = ctx.eAff.length := by rw [hR1_lo 3 (by decide)]; exact (hR0_lo 3 (by decide)).trans (by simp [startState])
  have hr4 : regs1 4 = ctx.wpPtr := by rw [hR1_lo 4 (by decide)]; exact (hR0_lo 4 (by decide)).trans (by simp [startState])
  have hr5 : regs1 5 = ctx.cand.length := by rw [hR1_lo 5 (by decide)]; exact (hR0_lo 5 (by decide)).trans (by simp [startState])
  have hr6 : regs1 6 = ctx.oldBucketsSum := by rw [hR1_lo 6 (by decide)]; exact (hR0_lo 6 (by decide)).trans (by simp [startState])
  have hr7 : regs1 7 = ctx.heapStep := by rw [hR1_lo 7 (by decide)]; exact (hR0_lo 7 (by decide)).trans (by simp [startState])
  have hr9 : regs1 9 = ctx.vCap := (hR1_lo 9 (by decide)).trans h0_9
  have hr10 : regs1 10 = ctx.eCap := (hR1_lo 10 (by decide)).trans h0_10
  have hr12 : regs1 12 = dsGPtr ctx.b := (hR1_lo 12 (by decide)).trans h0_12
  have hr13 : regs1 13 = dsHPtr ctx.b ctx.vCap ctx.eCap := (hR1_lo 13 (by decide)).trans h0_13
  have hr14 : regs1 14 = dsAuxPtr ctx.b ctx.vCap ctx.eCap := (hR1_lo 14 (by decide)).trans h0_14
  have hr15 : regs1 15 = dsMinHBase ctx.b ctx.vCap ctx.eCap := (hR1_lo 15 (by decide)).trans h0_15
  have hr16 : regs1 16 = dsHNextBase ctx.b ctx.vCap ctx.eCap := (hR1_lo 16 (by decide)).trans h0_16
  obtain ⟨hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr40⟩ := hR1_hi
  have hHS_lt_w : ctx.heapStep < 2 ^ ctx.w := by
    have h1 : ∀ (hs pw hh r1 ha sp cl el ls jn gb tw : ℕ),
        hs + 5 + pw ≤ hh → hh ≤ r1 → r1 ≤ ha →
        ha + 2 + sp + cl + el + el + 14 * ls + 15 * el + cl + 8 + 3 * jn + 11 * el + 10 * ls = gb →
        gb < tw → hs < tw := by intros; omega
    exact h1 _ _ _ _ _ _ _ _ _ _ _ _ ctx.hhead_in.1 ctx.hhead_in.2.1 ctx.hhead_in.2.2 rfl hwb.2.1
  -- Call 1: `lenSum := dsSumWalkLens [wpPtr, eAffLen]`
  refine runs_seq_call_le (vs := [ctx.wpPtr, ctx.eAff.length])
    (dsSumWalkLens_meetsContract (w := ctx.w) (es := ctx.eAff) (emb := ctx.piLt_mid) hp.hpAux)
    (evalArgs_cons (Expr.eval_reg_of_eq hr4) (evalArgs_cons (Expr.eval_reg_of_eq hr3) (evalArgs_nil _ _)))
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> omega)
    ⟨ctx.wpPtr, rfl, ctx.hw16, hwb.2.2.1, hwb.2.2.2.1, fun k' hk' =>
      ⟨(ctx.hAff_wp k' hk').2.2,
        lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (ctx.hAff_wp k' hk').2.1) hHS_lt_w⟩⟩ ?_
  rintro retLen mem1 pos1 ⟨hretLen, rfl⟩
  subst hretLen
  -- Assign `r25 := scratchPtr`, `r26 := J.n`, `r27 := guestBase`
  have hGB_sub :
      ctx.scratchPtr < 2 ^ ctx.w ∧ 14 * ctx.lenSum < 2 ^ ctx.w ∧
      15 * ctx.eAff.length < 2 ^ ctx.w ∧ 15 * ctx.eAff.length + ctx.cand.length < 2 ^ ctx.w ∧
      14 * ctx.lenSum + (15 * ctx.eAff.length + ctx.cand.length) < 2 ^ ctx.w ∧
      3 * ctx.J.n < 2 ^ ctx.w ∧ 11 * ctx.eAff.length < 2 ^ ctx.w ∧ 10 * ctx.lenSum < 2 ^ ctx.w ∧
      11 * ctx.eAff.length + 10 * ctx.lenSum < 2 ^ ctx.w ∧
      3 * ctx.J.n + (11 * ctx.eAff.length + 10 * ctx.lenSum) < 2 ^ ctx.w ∧
      8 + (3 * ctx.J.n + (11 * ctx.eAff.length + 10 * ctx.lenSum)) < 2 ^ ctx.w ∧
      ctx.scratchPtr + 1 < 2 ^ ctx.w := by
    have h1 : ∀ (wp el ls cl jn tw : ℕ),
        let scr := wp + el + 14 * ls + 15 * el + cl
        scr + 8 + 3 * jn + 11 * el + 10 * ls < tw →
        scr < tw ∧ 14 * ls < tw ∧ 15 * el < tw ∧ 15 * el + cl < tw ∧
        14 * ls + (15 * el + cl) < tw ∧ 3 * jn < tw ∧ 11 * el < tw ∧ 10 * ls < tw ∧
        11 * el + 10 * ls < tw ∧ 3 * jn + (11 * el + 10 * ls) < tw ∧
        8 + (3 * jn + (11 * el + 10 * ls)) < tw ∧ scr + 1 < tw := by
      intros; dsimp only at *; omega
    exact h1 ctx.wpPtr ctx.eAff.length ctx.lenSum ctx.cand.length ctx.J.n (2 ^ ctx.w) hwb.2.1
  have h16_lt : 16 < 2 ^ ctx.w := hwb.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hc_lt : ∀ n ≤ 16, n < 2 ^ ctx.w := fun _ hn => lt_of_le_of_lt hn h16_lt
  refine runs_seq_assign_le (v := ctx.scratchPtr)
    (by
      have h1 : ctx.scratchPtr = (ctx.wpPtr + ctx.eAff.length) +
          (14 * ctx.lenSum + (15 * ctx.eAff.length + ctx.cand.length)) := by
        dsimp only [StepPosNECtx.scratchPtr]; omega
      rw [h1]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr4]))
          (Expr.eval_reg_of_eq (by simp [hr3])) hwb.2.2.1)
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (hc_lt 14 (by decide)))
            (Expr.eval_reg_of_eq (by simp)) hGB_sub.2.1)
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (hc_lt 15 (by decide)))
              (Expr.eval_reg_of_eq (by simp [hr3])) hGB_sub.2.2.1)
            (Expr.eval_reg_of_eq (by simp [hr5])) hGB_sub.2.2.2.1)
          hGB_sub.2.2.2.2.1) (h1 ▸ hGB_sub.1)) ?_
  refine runs_seq_assign_le (v := ctx.J.n)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr14]))
      (Expr.eval_const (hc_lt dgNOff (by decide)))
      hwb.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hAuxN) ?_
  refine runs_seq_assign_le (v := ctx.guestBase)
    (by
      have h1 : ctx.guestBase = ctx.scratchPtr +
          (8 + (3 * ctx.J.n + (11 * ctx.eAff.length + 10 * ctx.lenSum))) := by
        dsimp only [StepPosNECtx.guestBase]; omega
      rw [h1]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add (Expr.eval_const (hc_lt 8 (by decide)))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (hc_lt 3 (by decide)))
              (Expr.eval_reg_of_eq (by simp)) hGB_sub.2.2.2.2.2.1)
            (Expr.eval_add
              (Expr.eval_mul (Expr.eval_const (hc_lt 11 (by decide)))
                (Expr.eval_reg_of_eq (by simp [hr3])) hGB_sub.2.2.2.2.2.2.1)
              (Expr.eval_mul (Expr.eval_const (hc_lt 10 (by decide)))
                (Expr.eval_reg_of_eq (by simp)) hGB_sub.2.2.2.2.2.2.2.1)
              hGB_sub.2.2.2.2.2.2.2.2.1) hGB_sub.2.2.2.2.2.2.2.2.2.1)
          hGB_sub.2.2.2.2.2.2.2.2.2.2.1) (h1 ▸ hwb.2.1)) ?_
  -- Call 2: `retSp := dsSparsifyStage [...]`
  obtain ⟨_, _, _, _, hFB_g, _, hFB_aux, _, _, hFB_sb, _, hFB_me, hFB_b⟩ :=
    stepPosNE_fixed_bases_lt_w ctx.b ctx.L ctx.vCap ctx.eCap (2 ^ ctx.w) hwb.1
  have heAff_lt : ctx.eAffPtr < 2 ^ ctx.w ∧ ctx.eAff.length < 2 ^ ctx.w ∧ ctx.wpPtr < 2 ^ ctx.w := by
    have h2 := hwb.2.2.1
    refine ⟨lt_of_le_of_lt (by dsimp only [StepPosNECtx.wpPtr]; omega) h2,
      lt_of_le_of_lt (by omega) h2, lt_of_le_of_lt (Nat.le_add_right _ _) h2⟩
  obtain ⟨hne, hJE_aff, hcanon, hJt_tail, hJt_head, hJt_E, hJt_walk, hembCap, hSpPre⟩ :=
    stepPosNE_spPre ctx
  refine runs_seq_call_le
    (vs := [dsGPtr ctx.b, dsAuxPtr ctx.b ctx.vCap ctx.eCap,
      dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.vCap, ctx.eCap,
      ctx.scratchPtr, ctx.guestBase, ctx.b, ctx.eAffPtr, ctx.eAff.length])
    (dsSparsifyStage_meetsContract ctx.impl ctx.mMax
      (w := ctx.w) (vCapH := ctx.vCap) (eCapH := ctx.eCap) (vCapJ := ctx.vCap) (eCapJ := ctx.eCap)
      (vCapOut := ctx.vCap) (eCapOut := ctx.eCap) (L := ctx.L) (vCap := ctx.vCap)
      (eCap := ctx.eCap) (b := ctx.b) (H' := ctx.G') (J := ctx.J) (emb := ctx.embJH) (eL := ctx.eAff)
      hp.hpSpDyn hp.hpGuest hp.hpFwd hp.hpEmit hp.hpRevDyn hp.hpRevCore hp.hpRevPrim hp.hpBatch
      hp.hpEdge hp.hpOps hp.hpGT hp.hpSort hp.hpLW hp.hpSS)
    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr12])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr14])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr23])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr9])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr10])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr0])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr2])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr3])) <|
      evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hFB_g
      · exact hFB_aux
      · exact hFB_me
      · exact hwb.2.2.2.2.2.2.2.1
      · exact hwb.2.2.2.2.2.2.2.2.1
      · exact hGB_sub.1
      · exact hwb.2.1
      · exact hFB_b
      · exact heAff_lt.1
      · exact heAff_lt.2.1)
    hSpPre ?_
  rintro retSp memSp posSp hSpPost
  obtain ⟨rc, hrc_w, hrc_v, hrc_e, hrc_G, hrc_eL, hrc_eJH, hrc_oE, hrc_S, hrc_es, hrc_gP, hrc_sB,
    hrc_tab, hrc_piT, hrc_esP, hrc_wpP, hrc_qTab, hrc_hp, hrc_m0, hgb_jt, hjt_q, hq_r1, hretSp_le,
    hDynJt, hZeroSp, hVSt_sp, hlt_scr_ag⟩ := stepPosNE_reembCtx ctx hSpPost
  have hjt_sp : memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp :=
    le_trans (le_of_eq hjt_q) (le_trans (Nat.le_add_right _ _) hq_r1)
  have hretSp_lt : retSp + ctx.eCap < 2 ^ ctx.w := by
    have h1 := spEnd_add_reemb_lt_of_end ctx.hEnd_ltw
    exact lt_of_le_of_lt (Nat.add_le_add_right hretSp_le _) (lt_of_le_of_lt (Nat.le_add_right _ _) h1)
  refine runs_seq_assign_le (v := memSp ctx.scratchPtr)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) rfl) ?_
  refine runs_seq_assign_le (v := memSp (ctx.scratchPtr + 1))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (hc_lt 1 (by decide))) hGB_sub.2.2.2.2.2.2.2.2.2.2.2) rfl) ?_
  refine runs_seq_assign_le (v := retSp + ctx.eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [hr10])) hretSp_lt) ?_
  -- Call 3: `retReemb := dsReembStage [...]`
  have hReMC : MeetsContract ctx.w p (bs.bRS + reembStageIdx) (dsReembStageContract rc) :=
    hrc_w ▸ dsReembStage_meetsContract rc hp.hpOps hp.hpRe hp.hpEmb hp.hpC hp.hpCA hp.hpRA hp.hpRS
  refine runs_seq_call_le
    (vs := [dsGPtr ctx.b, dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap,
      dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap, retSp, ctx.eAffPtr, ctx.eAff.length,
      ctx.wpPtr, memSp (ctx.scratchPtr + 1), retSp + ctx.eCap])
    hReMC
    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr12])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr21])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr23])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr2])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr3])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [hr4])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
      evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hFB_g
      · exact hFB_sb
      · exact hFB_me
      · exact lt_of_le_of_lt (Nat.le_add_right _ _) hretSp_lt
      · exact heAff_lt.1
      · exact heAff_lt.2.1
      · exact heAff_lt.2.2
      · exact lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) (le_trans hq_r1 (Nat.le_add_right _ _))) hretSp_lt
      · exact hretSp_lt)
    ⟨by simp only [hrc_gP, hrc_sB, hrc_tab, hrc_piT, hrc_esP, hrc_es, hrc_wpP, hrc_qTab, hrc_hp],
     hrc_m0.symm⟩ ?_
  rintro retReemb memReemb posRe hRePost
  refine stepPosNE_tail_run ctx hp hne hcanon hJt_E hembCap
    ⟨hrc_w, hrc_v, hrc_e, hrc_G, hrc_eL, hrc_eJH, hrc_oE, hrc_S, hrc_es, hrc_gP, hrc_sB,
     hrc_tab, hrc_piT, hrc_esP, hrc_wpP, hrc_hp, hrc_m0⟩
    ⟨hgb_jt, hjt_sp, hretSp_le, hDynJt, hZeroSp, hVSt_sp, hlt_scr_ag⟩ hRePost
    ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr6], by simp [hr7],
     by simp [hr9], by simp [hr10], by simp [hr12], by simp [hr13], by simp [hr15], by simp [hr16],
     by simp [hr17], by simp [hr18], by simp [hr19], by simp [hr20], by simp [hr22], by simp [hr23],
     by simp, by simp, by simp, by simp, by simp, by simp [hr40]⟩ ?_
  simp only [dsStepPosNonEmptyCost, dsSumWalkLensContract, dsReembStageContract,
    Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil,
    hrc_eL, hrc_eJH, hrc_oE, hrc_es]
  have hsp_eq : (dsSparsifyStageContract ctx.impl ctx.mMax ctx.w ctx.vCap ctx.eCap ctx.vCap ctx.eCap
      ctx.vCap ctx.eCap ctx.L ctx.vCap ctx.eCap ctx.b ctx.G' ctx.J ctx.embJH ctx.eAff).cost
      [dsGPtr ctx.b, dsAuxPtr ctx.b ctx.vCap ctx.eCap, dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap,
       ctx.vCap, ctx.eCap, ctx.scratchPtr, ctx.guestBase, ctx.b, ctx.eAffPtr, ctx.eAff.length]
      (startState [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
        ctx.oldBucketsSum, ctx.heapStep] ctx.memAff pos).mem =
      (dsSparsifyStageContract ctx.impl ctx.mMax 0 ctx.vCap ctx.eCap ctx.vCap ctx.eCap
      ctx.vCap ctx.eCap ctx.L ctx.vCap ctx.eCap 0 ctx.G' ctx.J ctx.embJH ctx.eAff).cost [] 0 := rfl
  rw [hsp_eq]
  have h1 : ∀ (a b c d e : ℕ),
      0 + 65 + 75 + (1 + (1 + 0)) + a + 2 +
        (1 + 1 + 1 + (1 + 1 + 1 + (1 + 1 + 1 + 1 + 1) + 1) + 1) +
        2 + (1 + 1 + 1 + 1) +
        2 + (1 + (1 + (1 + 1 + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1) + 1) + 1) +
        2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 0)))))))))) +
        b + 2 + (1 + 1) + 2 + (1 + 1 + 1 + 1) + 2 + (1 + 1 + 1) +
        2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 0))))))))) +
        c + 2 + d + e + 250 ≤ a + b + c + d + e + 600 := by
    intros; omega
  exact h1 _ _ _ _ _

end MinCostFlow.DynSpanner.Program
