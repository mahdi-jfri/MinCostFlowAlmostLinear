module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNERegs

/-!
# The nonempty `E_aff` branch of a `0 < j` step: the runs after `dsReembStage`

Proves `stepPosNE_tail_run`: from the post of `dsReembStage`, the rest of
`dsStepPosNonEmptyStmt` (`dsStepFinish`, the increment of `gen`, `dsCollectD` and the three
header words) runs within its cost and ends in `StepPosMidPost`. The run of `dsCollectD` and the
stores is `stepPosNE_col_run`.
-/

public section

namespace MinCostFlow.DynSpanner.Program

open WordRAM

/-- Final phase of `dsStepPosNonEmptyStmt` (after `dsStepFinish`): computes `dPtr`, bumps `gen`,
runs `dsCollectD`, stores `[uhTailHdr, dPtr, dLen]` at `heapStep..heapStep+2`, and returns. -/
private lemma stepPosNE_col_run (ctx : StepPosNECtx) {p : Program} {bs : StepPosNEBases}
    (hp : HasStepPosNEProcs ctx.impl p bs)
    {ω : ℕ → Bool} {memSp memReemb memFin : ℕ → ℕ}
    {retSp retReemb retFin posFin k : ℕ}
    {regs2 : ℕ → ℕ} {c : UTCtx} {r : RBCtx} {jtEList : List ℕ}
    (hne : ctx.E_aff.Nonempty)
    (hcanon : ctx.out = canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH)
    (hJt_E : ctx.out.Jtilde.E ⊆ ctx.E_aff)
    (hembCap : ∀ e ∈ ctx.E_aff, ∀ x ∈ ctx.embJH e, x.1 < ctx.eCap)
    (hSpInfo : ctx.guestBase ≤ memSp ctx.scratchPtr ∧
      memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp ∧
      retSp ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase ctx.G' ctx.J ctx.embJH +
        dsShortcutHeapSpace ctx.eAff ctx.out.emb ∧
      ∀ addr, addr < ctx.scratchPtr →
        (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
        memSp addr = ctx.memAff addr)
    (hRe_lt : ∀ addr < retSp, memReemb addr = memSp addr)
    (hRe_bnd :
      let heapFin := retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
        3 * (retReemb - (retSp + ctx.eCap))
      let uhTailHdr := heapFin + 2 * (retReemb - (retSp + ctx.eCap))
      retSp + ctx.eCap ≤ retReemb ∧
      retReemb - (retSp + ctx.eCap) ≤
        reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff ∧
      retReemb ≤ heapFin ∧
      heapFin + 2 * (ctx.eAff.map fun e =>
        (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e).length + 1).sum ≤
        uhTailHdr ∧
      ZeroFrom memReemb heapFin)
    (hjtInfo : jtEList.Nodup ∧ jtEList.length = ctx.out.Jtilde.m ∧
      (∀ e, e ∈ jtEList ↔ e ∈ ctx.out.Jtilde.E) ∧
      ListAt memReemb (dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap) jtEList)
    (hcInfo : c.da.w = ctx.w ∧ c.vCap = ctx.vCap ∧ c.da.eCap = ctx.eCap ∧
      c.da.lo = ctx.j ∧ c.da.hi = ctx.L + 1 ∧
      c.da.out = retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
        3 * (retReemb - (retSp + ctx.eCap)) + 2 * (retReemb - (retSp + ctx.eCap)) + 1 ∧
      c.es = jtEList ∧ c.size ≤ 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m)
    (hrInfo : r.L = ctx.L ∧ r.vCap = ctx.vCap ∧ r.eCap = ctx.eCap ∧ r.b = ctx.b ∧
      r.j = ctx.j ∧ r.es = jtEList)
    (hPermRecs : (restrictUpdate ctx.u ctx.st.H ++ c.recs).Perm ctx.res.UH)
    (hApplyRecs : (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)).applyBatch c.recs = ctx.res.state.H)
    (hDelIns : ∀ u' ∈ c.recs, isDelOrIns u')
    (hminNew : ∀ e < ctx.eCap,
      (minHRebuild ctx.j jtEList.toFinset r.m0 e = 0 ↔ e ∉ ctx.res.state.H.E) ∧
      (e ∈ ctx.res.state.H.E → ∃ i : Fin (ctx.L + 1),
        minHRebuild ctx.j jtEList.toFinset r.m0 e = i.1 + 1 ∧
        e ∈ (ctx.res.state.H_level i).E ∧
        ∀ k' : Fin (ctx.L + 1), k'.1 < i.1 → e ∉ (ctx.res.state.H_level k').E))
    (hnewB : ∀ i : Fin (ctx.L + 1), ∀ e, e ∈ r.newB i.1 ↔
      e ∈ ctx.res.state.H.E ∧ minHRebuild ctx.j jtEList.toFinset r.m0 e = i.1 + 1)
    (hFinPost :
      let heapFin := retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
        3 * (retReemb - (retSp + ctx.eCap))
      let uhTailHdr := heapFin + 2 * (retReemb - (retSp + ctx.eCap))
      (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
        uhTailHdr r ctx.G' ctx.eAff (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev)
        (fun _ => False) ctx.eAffPtr retSp heapFin).post
        ([dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dgEPresBase (memSp ctx.scratchPtr) ctx.vCap, uhTailHdr + 1,
          dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap, jtEList.length,
          dgEPresBase (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap,
          dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, uhTailHdr] ++
         [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b,
          dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap, jtEList.length] ++
         [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
          ctx.j + 1, ctx.j, ctx.L + 1] ++
         [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, retSp, heapFin])
        memReemb retFin memFin)
    (hFinPre_e : ∀ e ∈ ctx.eAff, retSp ≤ memReemb (retSp + e) ∧
      memReemb (retSp + e) +
        (mWalkEncode (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e)).length ≤
        retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
          3 * (retReemb - (retSp + ctx.eCap)))
    (hRegs2 :
      let uhTailHdr := retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
        3 * (retReemb - (retSp + ctx.eCap)) + 2 * (retReemb - (retSp + ctx.eCap))
      regs2 0 = ctx.b ∧ regs2 3 = ctx.eAff.length ∧ regs2 6 = ctx.oldBucketsSum ∧
      regs2 7 = ctx.heapStep ∧ regs2 22 = dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      regs2 23 = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧ regs2 24 = ctx.lenSum ∧
      regs2 35 = uhTailHdr ∧ regs2 36 = jtEList.length ∧
      regs2 38 = dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap)
    (hBnds :
      let uhTailHdr := retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
        3 * (retReemb - (retSp + ctx.eCap)) + 2 * (retReemb - (retSp + ctx.eCap))
      let dPtr := uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m
      16 < 2 ^ ctx.w ∧ ctx.b + dsGenOff < 2 ^ ctx.w ∧ uhTailHdr + 1 < 2 ^ ctx.w ∧
      dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap < 2 ^ ctx.w ∧
      jtEList.length < 2 ^ ctx.w ∧ dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap < 2 ^ ctx.w ∧
      dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap < 2 ^ ctx.w ∧
      2 * ctx.oldBucketsSum < 2 ^ ctx.w ∧ 4 * jtEList.length < 2 ^ ctx.w ∧
      2 * ctx.oldBucketsSum + 4 * jtEList.length < 2 ^ ctx.w ∧
      2 * ctx.lenSum < 2 ^ ctx.w ∧ 2 * ctx.lenSum + ctx.eAff.length < 2 ^ ctx.w ∧
      ctx.heapStep + 2 < 2 ^ ctx.w ∧ dPtr + (2 * ctx.lenSum + ctx.eAff.length) < 2 ^ ctx.w)
    (hk : k + (50 * (2 * ctx.lenSum + ctx.eAff.length) + 50 * ctx.out.Jtilde.m + 20) + 100 ≤
      dsStepPosNonEmptyCost ctx.impl ctx.mMax ctx.L ctx.vCap ctx.eCap ctx.j ctx.G' ctx.J
        ctx.piLt_mid ctx.embJH ctx.S_prev ctx.eAff ctx.oldBucketsSum) :
    ∃ o st' c0, Runs ctx.w p ω
      (.assign 42 (.bin .add (.bin .add (.reg 35) (.const 1))
         (.bin .add (.bin .mul (.const 2) (.reg 6)) (.bin .mul (.const 4) (.reg 36)))) ;;
       .assign 43 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
       .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 43) ;;
       .call 44 (bs.bCD + collectDIdx) [.reg 38, .reg 36, .reg 23, .reg 22, .reg 43, .reg 42] ;;
       .store (.reg 7) (.reg 35) ;;
       .store (.bin .add (.reg 7) (.const 1)) (.reg 42) ;;
       .store (.bin .add (.reg 7) (.const 2)) (.reg 44) ;;
       .ret (.bin .add (.reg 42) (.bin .add (.bin .mul (.const 2) (.reg 24)) (.reg 3))))
      { regs := regs2, mem := memFin, pos := posFin } o st' c0 ∧
      (dsStepPosNonEmptyContract ctx).post
        [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
          ctx.oldBucketsSum, ctx.heapStep] ctx.memAff o.value st'.mem ∧
      k + c0 ≤ (dsStepPosNonEmptyContract ctx).cost
        [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
          ctx.oldBucketsSum, ctx.heapStep] ctx.memAff := by
  obtain ⟨hgb_jt, hjt_sp, hretSp_le, hlt_scr_ag⟩ := hSpInfo
  obtain ⟨hret_ge_hr, hreemb_le_need, hret_le_hf, hSet_bnd, hZeroFin⟩ := hRe_bnd
  obtain ⟨hjt_nd, hjt_len, hjt_iff, hjt_at⟩ := hjtInfo
  obtain ⟨hc_w, hc_v, hc_e, hc_lo, hc_hi, hc_out, hc_es, hc_size_le⟩ := hcInfo
  obtain ⟨hr_L, hr_v, hr_e, hr_b, hr_j, hr_es⟩ := hrInfo
  obtain ⟨h2_0, h2_3, h2_6, h2_7, h2_22, h2_23, h2_24, h2_35, h2_36, h2_38⟩ := hRegs2
  obtain ⟨h16_lt, hgen_off_lt, huh1_lt, hjtE_lt, hjtL_lt, hFB_es, hFB_me, h2obs_lt, h4jt_lt,
    h2o4j_lt, h2ls_lt, h2lse_lt, hhs2_lt, hdPtr_lt⟩ := hBnds
  let reembDelta := retReemb - (retSp + ctx.eCap)
  let heapFin := retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum + 3 * reembDelta
  let uhTailHdr := heapFin + 2 * reembDelta
  let dPtr := uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m
  have hc_lt : ∀ n ≤ 16, n < 2 ^ ctx.w := fun _ hn => lt_of_le_of_lt hn h16_lt
  have hFinFr := stepPosNE_finFrame ctx (memSp := memSp) (memReemb := memReemb) (memFin := memFin)
    (retSp := retSp) (retReemb := retReemb) (retFin := retFin) (heapFin := heapFin)
    (uhTailHdr := uhTailHdr) (c := c) (r := r) (jtEList := jtEList) rfl rfl
    ⟨hgb_jt, hjt_sp, hlt_scr_ag⟩ hRe_lt
    ⟨hc_v, hc_e, hc_out⟩ ⟨hr_L, hr_v, hr_e, hr_b, hr_j⟩ hFinPost
  let memGen := Function.update memFin (ctx.b + dsGenOff) (memFin (ctx.b + dsGenOff) + 1)
  have hGen_lt : memFin (ctx.b + dsGenOff) + 1 < 2 ^ ctx.w := by
    rw [hFinFr.1]; have := ctx.hGen_ltw; omega
  refine runs_seq_assign_le (v := dPtr)
    (by
      have h1 : dPtr = (uhTailHdr + 1) + (2 * ctx.oldBucketsSum + 4 * jtEList.length) := by
        dsimp only [dPtr]; rw [hjt_len]; omega
      rw [h1]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq h2_35)
          (Expr.eval_const (hc_lt 1 (by decide))) huh1_lt)
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (hc_lt 2 (by decide)))
            (Expr.eval_reg_of_eq h2_6) h2obs_lt)
          (Expr.eval_mul (Expr.eval_const (hc_lt 4 (by decide)))
            (Expr.eval_reg_of_eq h2_36) h4jt_lt)
          h2o4j_lt)
        (h1 ▸ lt_of_le_of_lt (Nat.le_add_right _ _) hdPtr_lt)) ?_
  refine runs_seq_assign_le (v := memFin (ctx.b + dsGenOff) + 1)
    (Expr.eval_add
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2_0]))
          (Expr.eval_const (hc_lt dsGenOff (by decide))) hgen_off_lt) rfl)
      (Expr.eval_const (hc_lt 1 (by decide))) hGen_lt) ?_
  refine runs_seq_store_le (x := ctx.b + dsGenOff) (v := memFin (ctx.b + dsGenOff) + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2_0]))
      (Expr.eval_const (hc_lt dsGenOff (by decide))) hgen_off_lt)
    (Expr.eval_reg_of_eq (by simp)) ?_
  obtain ⟨dc, hdc_w, hdc_e, hdc_T, hdc_es, hdc_esP, hdc_tab, hdc_st, hdc_g, hdc_out, hdc_m0,
    hdTot⟩ :=
    stepPosNE_dCtx ctx (memSp := memSp) (memReemb := memReemb) (memFin := memFin) (memGen := memGen)
      (retSp := retSp) (retReemb := retReemb) (heapFin := heapFin) (uhTailHdr := uhTailHdr)
      (jtEList := jtEList) hJt_E hembCap rfl rfl ⟨hgb_jt, hjt_sp, hretSp_le, hlt_scr_ag⟩
      hRe_lt hreemb_le_need ⟨hjt_nd, hjt_len, hjt_iff, hjt_at⟩ hFinFr rfl
  -- Call 5: `dsCollectD`
  have hCDMC : MeetsContract ctx.w p (bs.bCD + collectDIdx) (dsCollectDContract dc) :=
    hdc_w ▸ dsCollectD_meetsContract dc hp.hpCD
  refine runs_seq_call_le
    (vs := [dc.esPtr, dc.es.length, dc.tab, dc.stamp, dc.g, dc.out])
    hCDMC
    (by
      rw [hdc_esP, hdc_es, hdc_tab, hdc_st, hdc_g, hdc_out]
      dsimp only [memGen]; rw [Function.update_self]
      exact evalArgs_cons (Expr.eval_reg_of_eq (by simp [h2_38])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [h2_36])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [h2_23])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [h2_22])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [dPtr])) <|
        evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [hdc_esP, hdc_es, hdc_tab, hdc_st, hdc_g, hdc_out] at hv
      dsimp only [memGen] at hv; rw [Function.update_self] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hjtE_lt
      · exact hjtL_lt
      · exact hFB_me
      · exact hFB_es
      · exact hGen_lt
      · exact lt_of_le_of_lt (Nat.le_add_right _ _) hdPtr_lt)
    ⟨rfl, hdc_m0.symm⟩ ?_
  rintro dLen memCol posCol hColPost
  let memFinal := Function.update
    (Function.update (Function.update memCol ctx.heapStep uhTailHdr) (ctx.heapStep + 1) dPtr)
    (ctx.heapStep + 2) dLen
  refine runs_seq_store_le (x := ctx.heapStep) (v := uhTailHdr)
    (Expr.eval_reg_of_eq (by simp [h2_7]))
    (Expr.eval_reg_of_eq (by simp [h2_35, uhTailHdr, heapFin, reembDelta])) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 1) (v := dPtr)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2_7]))
      (Expr.eval_const (hc_lt 1 (by decide))) (Nat.lt_of_succ_lt hhs2_lt))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 2) (v := dLen)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2_7]))
      (Expr.eval_const (hc_lt 2 (by decide))) hhs2_lt)
    (Expr.eval_reg_of_eq (by simp)) ?_
  obtain ⟨hMidPost, hAffAt, hAffLe⟩ := stepPosNE_midPost ctx (memSp := memSp) (memReemb := memReemb)
    (memFin := memFin) (memGen := memGen) (memCol := memCol) (memFinal := memFinal)
    (retSp := retSp) (retReemb := retReemb) (retFin := retFin) (dLen := dLen)
    (heapFin := heapFin) (uhTailHdr := uhTailHdr) (dPtr := dPtr) (c := c) (r := r)
    (jtEList := jtEList) (dc := dc) hne hcanon rfl rfl rfl ⟨hgb_jt, hjt_sp, hlt_scr_ag⟩ hRe_lt
    ⟨hret_ge_hr, hret_le_hf, hSet_bnd, hZeroFin⟩ ⟨hjt_nd, hjt_len, hjt_iff⟩
    ⟨hc_w, hc_v, hc_e, hc_lo, hc_hi, hc_out, hc_es, hc_size_le⟩
    ⟨hr_L, hr_v, hr_e, hr_b, hr_j, hr_es⟩
    hPermRecs hApplyRecs hDelIns hminNew hnewB hFinPost hFinPre_e rfl
    ⟨hdc_w, hdc_e, hdc_T, hdc_es, hdc_esP, hdc_tab, hdc_st, hdc_g, hdc_out, hdc_m0, hdTot⟩
    hColPost rfl
  have hRet_le : dPtr + 2 * ctx.lenSum + ctx.eAff.length ≤
      dsStepPosNonEmptyEnd ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.G' ctx.J
        ctx.piLt_mid ctx.embJH ctx.eAff ctx.wpPtr ctx.cand.length ctx.oldBucketsSum := by
    have h1 : ∀ (spEnd retS ec el ls rd rn ob jtm : ℕ),
        retS ≤ spEnd → rd ≤ rn →
        retS + ec + 16 * el + 14 * ls + 3 * rd + 2 * rd + 1 + 2 * ob + 4 * jtm + 2 * ls + el ≤
        spEnd + ec + 16 * el + 14 * ls + 5 * rn + 1 + 2 * ob + 4 * jtm + 2 * ls + el := by
      intros; omega
    exact h1 _ _ _ _ _ _ _ _ _ hretSp_le hreemb_le_need
  refine runs_ret_le (v := dPtr + 2 * ctx.lenSum + ctx.eAff.length)
    (by
      rw [Nat.add_assoc]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (hc_lt 2 (by decide)))
            (Expr.eval_reg_of_eq (by simp [h2_24])) h2ls_lt)
          (Expr.eval_reg_of_eq (by simp [h2_3])) h2lse_lt)
        hdPtr_lt)
    ⟨hMidPost, hRet_le, hAffAt, hAffLe⟩ ?_
  simp only [dsStepPosNonEmptyContract, dsCollectDContract,
    Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil,
    hdc_T, hdc_es, hjt_len]
  have h1 : ∀ (k0 jtM eLen dTot lenSum tot : ℕ),
      dTot ≤ 2 * lenSum + eLen →
      k0 + (50 * (2 * lenSum + eLen) + 50 * jtM + 20) + 100 ≤ tot →
      k0 + (1 + 1 + 1 + (1 + 1 + 1 + (1 + 1 + 1) + 1) + 1) + 2 +
        (1 + 1 + 1 + 1 + 1 + 1) + 2 + (1 + 1 + 1) + 1 + 2 +
        (1 + (1 + (1 + (1 + (1 + (1 + 0)))))) +
        (50 * dTot + 50 * jtM + 20) + 2 + 1 + 1 + 2 + (1 + 1 + 1) + 1 + 2 +
        (1 + 1 + 1) + 1 + 2 + (1 + (1 + 1 + 1 + 1 + 1) + 1 + 1) ≤ tot := by
    intros; omega
  exact h1 k ctx.out.Jtilde.m ctx.eAff.length (dTotal ctx.embJH jtEList) ctx.lenSum _ hdTot hk

private lemma stepPosNE_hPtr_add_dg_le (b L vCap eCap : ℕ) :
    dsHPtr b vCap eCap + (4 + 7 * vCap + 9 * eCap) ≤ b + dsFixedSize L vCap eCap := by
  obtain ⟨_, _, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    fixed_layout_order b L vCap eCap
  have : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  omega

private lemma stepPosNE_mid_arith (vc ec el ls rd obs jtm jtPtr retS hPtr hs tw : ℕ)
    (hH_hs : hPtr + (4 + 7 * vc + 9 * ec) ≤ hs)
    (hhs_ret : hs + 5 ≤ retS)
    (hjt_sp : jtPtr + (4 + 7 * vc + 9 * ec) ≤ retS)
    (hjt_le : jtm ≤ ec)
    (hlt :
      let hf := retS + ec + 16 * el + 14 * ls + 3 * rd
      let hdr := hf + 2 * rd
      hdr + 1 + 2 * obs + 4 * jtm + (2 * ls + el) < tw) :
    let hf := retS + ec + 16 * el + 14 * ls + 3 * rd
    let hdr := hf + 2 * rd
    rd < tw ∧ hf < tw ∧ hdr + 1 < tw ∧ jtPtr + 3 < tw ∧
    jtPtr + 4 + 7 * vc < tw ∧ jtPtr + 4 + 7 * vc + ec < tw ∧
    hPtr + 4 + 7 * vc < tw ∧ jtm < tw ∧
    16 * el < tw ∧ 14 * ls < tw ∧ 3 * rd < tw ∧ 14 * ls + 3 * rd < tw ∧
    16 * el + (14 * ls + 3 * rd) < tw ∧ 2 * rd < tw ∧ jtPtr + 4 < tw ∧
    7 * vc < tw ∧ hPtr + 4 < tw ∧ 2 * obs < tw ∧ 4 * jtm < tw ∧
    2 * obs + 4 * jtm < tw ∧ 2 * ls < tw ∧ 2 * ls + el < tw ∧ hs + 2 < tw := by
  dsimp only at hlt ⊢; omega

/-- Second half of `dsStepPosNonEmptyStmt`, from `r33` (`reembDelta`) through `dsStepFinish`,
`gen++`, `dsCollectD`, the three-word header store, and `ret`. -/
lemma stepPosNE_tail_run (ctx : StepPosNECtx) {p : Program} {bs : StepPosNEBases}
    (hp : HasStepPosNEProcs ctx.impl p bs)
    {ω : ℕ → Bool} {memSp memReemb : ℕ → ℕ} {retSp retReemb posRe k : ℕ}
    {regs : ℕ → ℕ} {rc : RSCtx}
    (hne : ctx.E_aff.Nonempty)
    (hcanon : ctx.out = canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH)
    (hJt_E : ctx.out.Jtilde.E ⊆ ctx.E_aff)
    (hembCap : ∀ e ∈ ctx.E_aff, ∀ x ∈ ctx.embJH e, x.1 < ctx.eCap)
    (hrc : rc.w = ctx.w ∧ rc.vCap = ctx.vCap ∧ rc.eCap = ctx.eCap ∧
      rc.G = ctx.G' ∧ rc.embLt = ctx.piLt_mid ∧ rc.embJH = ctx.embJH ∧
      rc.outEmb = ctx.outEmb ∧ rc.S = ctx.S_prev ∧ rc.es = ctx.eAff ∧
      rc.gPtr = dsGPtr ctx.b ∧ rc.sBitPtr = dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      rc.tab = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧ rc.piTab = retSp ∧
      rc.esPtr = ctx.eAffPtr ∧ rc.wpPtr = ctx.wpPtr ∧ rc.heap = retSp + ctx.eCap ∧
      rc.mem0 = memSp)
    (hSpInfo : ctx.guestBase ≤ memSp ctx.scratchPtr ∧
      memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp ∧
      retSp ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase ctx.G' ctx.J ctx.embJH +
        dsShortcutHeapSpace ctx.eAff ctx.out.emb ∧
      DynGraphAt memSp (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ctx.out.Jtilde ∧
      ZeroFrom memSp retSp ∧
      (∀ v < ctx.vCap, memSp (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) ≤
        ctx.memAff (ctx.b + dsGenOff)) ∧
      (∀ addr, addr < ctx.scratchPtr →
        (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
        memSp addr = ctx.memAff addr))
    (hRePost : (dsReembStageContract rc).post [] memSp retReemb memReemb)
    (hRegs :
      regs 0 = ctx.b ∧ regs 1 = ctx.j ∧ regs 2 = ctx.eAffPtr ∧ regs 3 = ctx.eAff.length ∧
      regs 6 = ctx.oldBucketsSum ∧ regs 7 = ctx.heapStep ∧ regs 9 = ctx.vCap ∧ regs 10 = ctx.eCap ∧
      regs 12 = dsGPtr ctx.b ∧ regs 13 = dsHPtr ctx.b ctx.vCap ctx.eCap ∧
      regs 15 = dsMinHBase ctx.b ctx.vCap ctx.eCap ∧
      regs 16 = dsHNextBase ctx.b ctx.vCap ctx.eCap ∧
      regs 17 = dsHHeadBase ctx.b ctx.vCap ctx.eCap ∧
      regs 18 = dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      regs 19 = dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      regs 20 = dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      regs 22 = dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      regs 23 = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      regs 24 = ctx.lenSum ∧ regs 28 = retSp ∧ regs 29 = memSp ctx.scratchPtr ∧
      regs 31 = retSp + ctx.eCap ∧ regs 32 = retReemb ∧ regs 40 = ctx.L + 1)
    (hk : k +
      (100 * ctx.oldBucketsSum + 150 * (ctx.L + 1 - ctx.j) + 420 * ctx.out.Jtilde.m +
       670 * (2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m) +
       400 * (ctx.eAff.map fun e =>
         (reembedWalk ctx.G' ctx.G' ctx.piLt_mid ctx.embMid ctx.S_prev e).length).sum +
       620 * ctx.eAff.length + 1800) +
      (50 * (2 * ctx.lenSum + ctx.eAff.length) + 50 * ctx.out.Jtilde.m + 20) + 250 ≤
      dsStepPosNonEmptyCost ctx.impl ctx.mMax ctx.L ctx.vCap ctx.eCap ctx.j ctx.G' ctx.J
        ctx.piLt_mid ctx.embJH ctx.S_prev ctx.eAff ctx.oldBucketsSum) :
    ∃ o st' c, Runs ctx.w p ω
      (.assign 33 (.bin .sub (.reg 32) (.reg 31)) ;;
       .assign 34 (.bin .add (.reg 31)
         (.bin .add (.bin .mul (.const 16) (.reg 3))
           (.bin .add (.bin .mul (.const 14) (.reg 24)) (.bin .mul (.const 3) (.reg 33))))) ;;
       .assign 35 (.bin .add (.reg 34) (.bin .mul (.const 2) (.reg 33))) ;;
       .assign 36 (.load (.bin .add (.reg 29) (.const dgMOff))) ;;
       .assign 37 (.bin .add (.bin .add (.reg 29) (.const 4)) (.bin .mul (.const 7) (.reg 9))) ;;
       .assign 38 (.bin .add (.reg 37) (.reg 10)) ;;
       .assign 39 (.bin .add (.bin .add (.reg 13) (.const 4)) (.bin .mul (.const 7) (.reg 9))) ;;
       .call 41 (bs.bFin + stepFinishIdx)
         [.reg 16, .reg 17, .reg 18, .reg 1, .reg 40, .reg 37, .bin .add (.reg 35) (.const 1),
          .reg 38, .reg 36, .reg 39, .reg 12, .reg 13, .reg 35,
          .reg 16, .reg 17, .reg 18, .reg 1, .reg 40, .reg 15, .reg 0, .reg 38, .reg 36,
          .reg 19, .reg 20, .bin .add (.reg 1) (.const 1), .reg 1, .reg 40,
          .reg 0, .reg 1, .reg 2, .reg 3, .reg 28, .reg 34] ;;
       .assign 42 (.bin .add (.bin .add (.reg 35) (.const 1))
         (.bin .add (.bin .mul (.const 2) (.reg 6)) (.bin .mul (.const 4) (.reg 36)))) ;;
       .assign 43 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
       .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 43) ;;
       .call 44 (bs.bCD + collectDIdx) [.reg 38, .reg 36, .reg 23, .reg 22, .reg 43, .reg 42] ;;
       .store (.reg 7) (.reg 35) ;;
       .store (.bin .add (.reg 7) (.const 1)) (.reg 42) ;;
       .store (.bin .add (.reg 7) (.const 2)) (.reg 44) ;;
       .ret (.bin .add (.reg 42) (.bin .add (.bin .mul (.const 2) (.reg 24)) (.reg 3))))
      { regs := regs, mem := memReemb, pos := posRe } o st' c ∧
      (dsStepPosNonEmptyContract ctx).post
        [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
          ctx.oldBucketsSum, ctx.heapStep] ctx.memAff o.value st'.mem ∧
      k + c ≤ (dsStepPosNonEmptyContract ctx).cost
        [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
          ctx.oldBucketsSum, ctx.heapStep] ctx.memAff := by
  have hwb := stepPosNE_word_bounds ctx
  obtain ⟨hgb_jt, hjt_sp, hretSp_le, hDynJt, hZeroSp, hVSt_sp, hlt_scr_ag⟩ := hSpInfo
  obtain ⟨hr0, hr1, hr2, hr3, hr6, hr7, hr9, hr10, hr12, hr13, hr15, hr16, hr17, hr18, hr19, hr20,
    hr22, hr23, hr24, hr28, hr29, hr31, hr32, hr40⟩ := hRegs
  obtain ⟨c, r, jtEList, hjt_nd, hjt_len, hjt_iff, hjt_at, hret_ge_hr, hreemb_le_need,
    hRe_bounds, hret_le_hf, hSet_bnd, hZeroFin, hc_w, hc_v, hc_e, hc_lo, hc_hi, hc_out,
    hc_es, hc_size_le, hc_bk, hr_L, hr_v, hr_e, hr_b, hr_j, hr_es, hr_bk, hPermRecs, hApplyRecs,
    hDelIns, hminNew, hnewB, hFinPre, hRe_lt⟩ :=
    stepPosNE_finPre ctx hne hcanon hJt_E hrc
      ⟨hgb_jt, hjt_sp, hretSp_le, hDynJt, hZeroSp, hVSt_sp, hlt_scr_ag⟩ hRePost
  have hdEnd := ctx.dPtr_lt hretSp_le hreemb_le_need
  have hjtM_re : memReemb (memSp ctx.scratchPtr + dgMOff) = jtEList.length := by
    rw [hRe_lt _ (by dsimp only [dgMOff, dynGraphSize] at hjt_sp ⊢; omega),
      hDynJt.2.2.2.2.2.2.1, hjt_len]
  let reembDelta := retReemb - (retSp + ctx.eCap)
  let heapFin := retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum + 3 * reembDelta
  let uhTailHdr := heapFin + 2 * reembDelta
  let jtPres := dgEPresBase (memSp ctx.scratchPtr) ctx.vCap
  let jtEListPtr := dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap
  let hPres := dgEPresBase (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap
  let dPtr := uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m
  have hdPtr_lt : dPtr + (2 * ctx.lenSum + ctx.eAff.length) < 2 ^ ctx.w := by
    have : uhTailHdr = retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
        5 * (retReemb - (retSp + ctx.eCap)) := by dsimp only [uhTailHdr, heapFin, reembDelta]; omega
    show uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m +
      (2 * ctx.lenSum + ctx.eAff.length) < 2 ^ ctx.w
    rw [this]; exact hdEnd
  have hjt_le : jtEList.length ≤ ctx.eCap := by
    rw [hjt_len]
    have hsub : ctx.out.Jtilde.E ⊆ Finset.range ctx.eCap := fun e he =>
      Finset.mem_range.mpr (hDynJt.2.2.1 e he)
    exact le_trans (Finset.card_le_card hsub) (by simp)
  have hH_hs : dsHPtr ctx.b ctx.vCap ctx.eCap + (4 + 7 * ctx.vCap + 9 * ctx.eCap) ≤ ctx.heapStep :=
    le_trans (stepPosNE_hPtr_add_dg_le ctx.b ctx.L ctx.vCap ctx.eCap) ctx.hfix_step
  have hhs_ret : ctx.heapStep + 5 ≤ retSp := by
    have h2 : ∀ (hs pw hh r1 ha sp cl el ls scr gb jt dg rs : ℕ),
        hs + 5 + pw ≤ hh → hh ≤ r1 → r1 ≤ ha →
        ha + 2 + sp + cl + el + el + 14 * ls + 15 * el + cl = scr →
        scr + 8 + 3 * ctx.J.n + 11 * el + 10 * ls = gb →
        gb ≤ jt → jt + dg ≤ rs → hs + 5 ≤ rs := by intros; omega
    exact h2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ctx.hhead_in.1 ctx.hhead_in.2.1 ctx.hhead_in.2.2
      rfl rfl hgb_jt hjt_sp
  have hlt' : uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * jtEList.length +
      (2 * ctx.lenSum + ctx.eAff.length) < 2 ^ ctx.w := by rw [hjt_len]; exact hdPtr_lt
  obtain ⟨_, hMW_hf, hMW_uh1, hMW_jtM, hMW_jtP, hMW_jtE, hMW_hP, hMW_jtL, hMW_16e, hMW_14l,
    hMW_3r, hMW_14_3, hMW_16_14, hMW_2r, hMW_jt4, hMW_7v, hMW_h4, hMW_2o, hMW_4j, hMW_2o4j,
    hMW_2l, hMW_2le, hMW_hs2⟩ :=
    stepPosNE_mid_arith ctx.vCap ctx.eCap ctx.eAff.length ctx.lenSum reembDelta ctx.oldBucketsSum
      jtEList.length (memSp ctx.scratchPtr) retSp (dsHPtr ctx.b ctx.vCap ctx.eCap)
      ctx.heapStep (2 ^ ctx.w) hH_hs hhs_ret hjt_sp hjt_le hlt'
  obtain ⟨hwb_fix, _, hwb_wp, _, _, hwb_j1, hwb_L1, _, _, _, _, _, hwb_gen, _, h16_lt⟩ := hwb
  have hc_lt : ∀ n ≤ 16, n < 2 ^ ctx.w := fun _ hn => lt_of_le_of_lt hn h16_lt
  refine stepPosNE_fin_regs h16_lt hr3 hr9 hr10 hr13 hr24 hr29 hr31 hr32 hjtM_re
    (lt_of_le_of_lt hret_le_hf hMW_hf)
    ⟨hMW_hf, Nat.lt_of_succ_lt hMW_uh1, hMW_jtM, hMW_jtP, hMW_jtE, hMW_hP, hMW_16e, hMW_14l,
     hMW_3r, hMW_14_3, hMW_16_14, hMW_2r, hMW_jt4, hMW_7v, hMW_h4⟩ ?_
  intro regs2 hR2_old hR2_new
  obtain ⟨_, h2_34, h2_35, h2_36, h2_37, h2_38, h2_39⟩ := hR2_new
  have h2_0 : regs2 0 = ctx.b := (hR2_old 0 (by omega)).trans hr0
  have h2_1 : regs2 1 = ctx.j := (hR2_old 1 (by omega)).trans hr1
  have h2_2 : regs2 2 = ctx.eAffPtr := (hR2_old 2 (by omega)).trans hr2
  have h2_3 : regs2 3 = ctx.eAff.length := (hR2_old 3 (by omega)).trans hr3
  have h2_6 : regs2 6 = ctx.oldBucketsSum := (hR2_old 6 (by omega)).trans hr6
  have h2_7 : regs2 7 = ctx.heapStep := (hR2_old 7 (by omega)).trans hr7
  have h2_12 : regs2 12 = dsGPtr ctx.b := (hR2_old 12 (by omega)).trans hr12
  have h2_13 : regs2 13 = dsHPtr ctx.b ctx.vCap ctx.eCap := (hR2_old 13 (by omega)).trans hr13
  have h2_15 : regs2 15 = dsMinHBase ctx.b ctx.vCap ctx.eCap := (hR2_old 15 (by omega)).trans hr15
  have h2_16 : regs2 16 = dsHNextBase ctx.b ctx.vCap ctx.eCap := (hR2_old 16 (by omega)).trans hr16
  have h2_17 : regs2 17 = dsHHeadBase ctx.b ctx.vCap ctx.eCap := (hR2_old 17 (by omega)).trans hr17
  have h2_18 : regs2 18 = dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap := (hR2_old 18 (by omega)).trans hr18
  have h2_19 : regs2 19 = dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap := (hR2_old 19 (by omega)).trans hr19
  have h2_20 : regs2 20 = dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap := (hR2_old 20 (by omega)).trans hr20
  have h2_22 : regs2 22 = dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap := (hR2_old 22 (by omega)).trans hr22
  have h2_23 : regs2 23 = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap := (hR2_old 23 (by omega)).trans hr23
  have h2_24 : regs2 24 = ctx.lenSum := (hR2_old 24 (by omega)).trans hr24
  have h2_28 : regs2 28 = retSp := (hR2_old 28 (by omega)).trans hr28
  have h2_40 : regs2 40 = ctx.L + 1 := (hR2_old 40 (by omega)).trans hr40
  -- Call 4: `dsStepFinish`
  let Pi_j := reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev
  obtain ⟨hFB_hn, hFB_hh, hFB_hd, hFB_mh, hFB_g, hFB_h, _, hFB_dg, hFB_sg, _, hFB_es, hFB_me, hFB_b⟩ :=
    stepPosNE_fixed_bases_lt_w ctx.b ctx.L ctx.vCap ctx.eCap (2 ^ ctx.w) hwb_fix
  have hrsp_lt : retSp < 2 ^ ctx.w :=
    lt_of_le_of_lt (show retSp ≤ heapFin by dsimp only [heapFin]; omega) hMW_hf
  have he1_lt : ctx.eAffPtr < 2 ^ ctx.w :=
    lt_of_le_of_lt (show ctx.eAffPtr ≤ ctx.wpPtr + ctx.eAff.length by
      dsimp only [StepPosNECtx.wpPtr]; omega) hwb_wp
  have he2_lt : ctx.eAff.length < 2 ^ ctx.w :=
    lt_of_le_of_lt (Nat.le_add_left _ _) hwb_wp
  have hj1_lt : ctx.j < 2 ^ ctx.w := Nat.lt_of_succ_lt hwb_j1
  have hu1_lt : uhTailHdr < 2 ^ ctx.w := Nat.lt_of_succ_lt hMW_uh1
  have hFinMC : MeetsContract ctx.w p (bs.bFin + stepFinishIdx)
      (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
        uhTailHdr r ctx.G' ctx.eAff Pi_j (fun _ => False) ctx.eAffPtr retSp heapFin) :=
    hc_w ▸ dsStepFinish_meetsContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
      uhTailHdr r ctx.G' ctx.eAff Pi_j (fun _ => False) ctx.eAffPtr retSp heapFin
      hp.hpDR hp.hpDA hp.hpOps hp.hpIR hp.hpUT hp.hpBatch hp.hpEdge hp.hpSplit hp.hpAU hp.hpUE
      hp.hpCB hp.hpPhase hp.hpFL hp.hpRB hp.hpSE hp.hpZ hp.hpClrA hp.hpST hp.hpLW hp.hpRev
      hp.hpFin
  refine runs_seq_call_le
    (vs := [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
      dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
      jtPres, uhTailHdr + 1, jtEListPtr, jtEList.length, hPres,
      dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, uhTailHdr] ++
     [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
      dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
      dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b, jtEListPtr, jtEList.length] ++
     [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
      ctx.j + 1, ctx.j, ctx.L + 1] ++
     [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, retSp, heapFin])
    hFinMC
    (by
      simp only [List.cons_append, List.nil_append]
      exact evalArgs_cons (Expr.eval_reg_of_eq h2_16) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_17) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_18) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_40) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_37) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq h2_35)
          (Expr.eval_const (hc_lt 1 (by decide))) hMW_uh1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_38) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_36) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_39) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_12) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_13) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_35) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_16) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_17) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_18) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_40) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_15) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_0) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_38) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_36) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_19) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_20) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq h2_1)
          (Expr.eval_const (hc_lt 1 (by decide))) hwb_j1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_40) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_0) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_2) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_3) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_28) <|
        evalArgs_cons (Expr.eval_reg_of_eq h2_34) <|
        evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · exact hFB_hn
      · exact hFB_hh
      · exact hFB_hd
      · exact hj1_lt
      · exact hwb_L1
      · exact hMW_jtP
      · exact hMW_uh1
      · exact hMW_jtE
      · exact hMW_jtL
      · exact hMW_hP
      · exact hFB_g
      · exact hFB_h
      · exact hu1_lt
      · exact hFB_hn
      · exact hFB_hh
      · exact hFB_hd
      · exact hj1_lt
      · exact hwb_L1
      · exact hFB_mh
      · exact hFB_b
      · exact hMW_jtE
      · exact hMW_jtL
      · exact hFB_dg
      · exact hFB_sg
      · exact hwb_j1
      · exact hj1_lt
      · exact hwb_L1
      · exact hFB_b
      · exact hj1_lt
      · exact he1_lt
      · exact he2_lt
      · exact hrsp_lt
      · exact hMW_hf)
    hFinPre ?_
  rintro retFin memFin posFin hFinPost
  have hPi_congr : ∀ e, Pi_j e = reembedWalk ctx.G' ctx.G' ctx.piLt_mid ctx.embMid ctx.S_prev e :=
    fun e => (reembedWalk_congr_host (H_lt := ctx.H_lt)
      (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).tail = ctx.G'.tail)
      (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).head = ctx.G'.head) _ _ _ _).symm
  have hFinPre_e : ∀ e ∈ ctx.eAff, retSp ≤ memReemb (retSp + e) ∧
      memReemb (retSp + e) + (mWalkEncode (Pi_j e)).length ≤ heapFin := by
    intro e he
    have h1 := hRePost.1 e (by rw [hrc.2.2.2.2.2.2.2.2.1]; exact he)
    rw [hrc.2.2.2.2.2.2.2.2.2.2.2.2.1, hrc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hrc.2.2.2.2.2.2.2.2.1, hrc.2.2.2.2.2.1, hrc.2.2.2.2.2.2.1, hrc.2.2.2.1, hrc.2.2.2.2.1,
      hrc.2.2.2.2.2.2.2.1] at h1
    have hlen : (mWalkEncode (Pi_j e)).length =
        reembOutLen ctx.G' ctx.piLt_mid ctx.embMid ctx.S_prev e := by
      rw [hPi_congr e, mWalkEncode_length, reembOutLen, Nat.add_comm]
    exact ⟨le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) h1.1)),
      by rw [hlen]; exact le_trans h1.2.1 hret_le_hf⟩
  refine stepPosNE_col_run ctx hp hne hcanon hJt_E hembCap
    ⟨hgb_jt, hjt_sp, hretSp_le, hlt_scr_ag⟩ hRe_lt
    ⟨hret_ge_hr, hreemb_le_need, hret_le_hf, hSet_bnd, hZeroFin⟩
    ⟨hjt_nd, hjt_len, hjt_iff, hjt_at⟩
    ⟨hc_w, hc_v, hc_e, hc_lo, hc_hi, hc_out, hc_es, hc_size_le⟩
    ⟨hr_L, hr_v, hr_e, hr_b, hr_j, hr_es⟩
    hPermRecs hApplyRecs hDelIns hminNew hnewB hFinPost hFinPre_e
    ⟨by simp [h2_0], by simp [h2_3], by simp [h2_6], by simp [h2_7], by simp [h2_22],
     by simp [h2_23], by simp [h2_24], by simp [h2_35], by simp [h2_36], by simp [h2_38]⟩
    ⟨h16_lt, hwb_gen, hMW_uh1, hMW_jtE, hMW_jtL, hFB_es, hFB_me, hMW_2o, hMW_4j, hMW_2o4j,
     hMW_2l, hMW_2le, hMW_hs2, hdPtr_lt⟩ ?_
  have hPi_sum_eq : (ctx.eAff.map fun e => (Pi_j e).length).sum =
      (ctx.eAff.map fun e => (reembedWalk ctx.G' ctx.G' ctx.piLt_mid ctx.embMid ctx.S_prev e).length).sum :=
    congrArg List.sum (List.map_congr_left fun e _ => congrArg List.length (hPi_congr e))
  have hfin_cost :
      (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
        uhTailHdr r ctx.G' ctx.eAff Pi_j (fun _ => False) ctx.eAffPtr retSp heapFin).cost
        ([dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          jtPres, uhTailHdr + 1, jtEListPtr, jtEList.length, hPres,
          dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, uhTailHdr] ++
         [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b, jtEListPtr, jtEList.length] ++
         [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
          ctx.j + 1, ctx.j, ctx.L + 1] ++
         [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, retSp, heapFin]) memReemb ≤
      100 * ctx.oldBucketsSum + 150 * (ctx.L + 1 - ctx.j) + 420 * ctx.out.Jtilde.m +
        670 * (2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m) +
        400 * (ctx.eAff.map fun e => (reembedWalk ctx.G' ctx.G' ctx.piLt_mid ctx.embMid ctx.S_prev e).length).sum +
        620 * ctx.eAff.length + 1800 := by
    dsimp only [dsStepFinishContract]
    rw [hc_bk, hr_bk, hc_lo, hc_hi, hr_L, hr_j, hc_es, hr_es, hjt_len, hPi_sum_eq]
    have h0 : ∀ (a b d e f g : ℕ), e ≤ 2 * a + 4 * d →
        60 * a + 60 * b + 210 * d + 670 * e + 40 * a + 60 * b + 210 * d + 30 * b +
          400 * f + 620 * g + 1800 ≤
        100 * a + 150 * b + 420 * d + 670 * (2 * a + 4 * d) + 400 * f + 620 * g + 1800 := by
      intros; omega
    exact h0 _ _ _ _ _ _ hc_size_le
  have hargs_sz : argsSize
      [.reg 16, .reg 17, .reg 18, .reg 1, .reg 40, .reg 37, .bin .add (.reg 35) (.const 1),
       .reg 38, .reg 36, .reg 39, .reg 12, .reg 13, .reg 35,
       .reg 16, .reg 17, .reg 18, .reg 1, .reg 40, .reg 15, .reg 0, .reg 38, .reg 36,
       .reg 19, .reg 20, .bin .add (.reg 1) (.const 1), .reg 1, .reg 40,
       .reg 0, .reg 1, .reg 2, .reg 3, .reg 28, .reg 34] = 37 := by decide
  rw [hargs_sz]
  have h1 : ∀ (k0 fc fb dc tot : ℕ), fc ≤ fb → k0 + fb + dc + 250 ≤ tot →
      k0 + 66 + 37 + fc + 2 + dc + 100 ≤ tot := by intros; omega
  exact h1 k _ _ _ _ hfin_cost hk

end MinCostFlow.DynSpanner.Program
