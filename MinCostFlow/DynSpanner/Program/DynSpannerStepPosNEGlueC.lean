module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueB
import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEFrames

/-!
# Post-stage assembly for the nonempty `E_aff` branch of a positive-level step

This file proves `stepPosNE_midPost`, assembling the unified post-branch invariant `StepPosMidPost`
on the final memory of `dsStepPosNonEmptyStmt` from the stage postconditions of
`dsSparsifyStage`, `dsReembStage`, `dsStepFinish`, the generation bump `gen++`, `dsCollectD`,
and the three-word header write `[uhTailHdr, dPtr, dLen]` at `heapStep`.
-/

public section

namespace MinCostFlow.DynSpanner.Program

open WordRAM

/-- Algebraic identities for `ctx.res` when `0 < ctx.j` and `ctx.E_aff.Nonempty`. -/
lemma stepPosNE_res_eqs (ctx : StepPosNECtx)
    (hne : ctx.E_aff.Nonempty)
    (hcanon : ctx.out = canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH) :
    let jF : Fin (ctx.L + 1) := ⟨ctx.j, Nat.lt_succ_of_le (chooseLevel_le ctx.L ctx.q (ctx.k + 1))⟩
    ctx.res.state.G = ctx.G' ∧
    ctx.res.state.inDom jF = ctx.E_aff ∧
    ctx.res.state.Pi_level jF =
      reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev ∧
    ctx.res.D = ctx.out.Jtilde.E.biUnion (fun e => walkEdges (ctx.embJH e)) := by
  have hk := ctx.hPref ctx.k (le_refl _)
  have ht : ctx.st.t = ctx.k := hk.t_eq
  have hq : ctx.st.q = ctx.q := hk.q_eq
  have hjne : chooseLevel ctx.L ctx.q (ctx.k + 1) ≠ 0 := Nat.ne_of_gt ctx.hj_pos
  have hstep : ctx.res = step ctx.st ctx.u (canonicalSparsify ctx.impl) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hstep, step, ht, hq, hjne, ↓reduceDIte]
  · simp only [hstep, step, ht, hq, hjne, ↓reduceDIte, lt_irrefl, ↓reduceIte]
  · simp only [hstep, step, ht, hq, hjne, ↓reduceDIte, lt_irrefl, ↓reduceIte, hne, ← hcanon]
  · simp only [hstep, step, ht, hq, hjne, ↓reduceDIte]
    change (if ctx.E_aff.Nonempty then canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH
      else _).Jtilde.E.biUnion (fun e => walkEdges (ctx.embJH e)) = _
    simp only [hne, ↓reduceIte, ← hcanon]

private lemma not_genWord_of_outside {r : RBCtx} {b L vCap eCap j a : ℕ}
    (hr_b : r.b = b) (hr_L : r.L = L) (hr_v : r.vCap = vCap) (hr_e : r.eCap = eCap) (hr_j : r.j = j)
    (h4 : a < dsDomGenBase b L vCap eCap + (j + 1) ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ a)
    (h5 : a < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ a) :
    ¬ r.GenWord a := by
  intro hgw
  simp only [RBCtx.GenWord, hr_b, hr_L, hr_v, hr_e, hr_j] at hgw
  omega

/-- Assemble `StepPosMidPost` on `memFinal` from the postconditions of all sub-calls in
`dsStepPosNonEmptyStmt`. -/
theorem stepPosNE_midPost (ctx : StepPosNECtx)
    {memSp memReemb memFin memGen memCol memFinal : ℕ → ℕ}
    {retSp retReemb retFin dLen heapFin uhTailHdr dPtr : ℕ}
    {c : UTCtx} {r : RBCtx} {jtEList : List ℕ} {dc : DCtx}
    (hne : ctx.E_aff.Nonempty)
    (hcanon : ctx.out = canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH)
    (hhf : heapFin = retSp + ctx.eCap + 16 * ctx.eAff.length + 14 * ctx.lenSum +
      3 * (retReemb - (retSp + ctx.eCap)))
    (hhdr : uhTailHdr = heapFin + 2 * (retReemb - (retSp + ctx.eCap)))
    (hdPtr : dPtr = uhTailHdr + 1 + 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m)
    (hSpInfo : ctx.guestBase ≤ memSp ctx.scratchPtr ∧
      memSp ctx.scratchPtr + dynGraphSize ctx.vCap ctx.eCap ≤ retSp ∧
      (∀ addr, addr < ctx.scratchPtr →
        (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
        memSp addr = ctx.memAff addr))
    (hRe_lt : ∀ addr, addr < retSp → memReemb addr = memSp addr)
    (hRe_bounds : retSp + ctx.eCap ≤ retReemb ∧ retReemb ≤ heapFin ∧
      heapFin + 2 * (ctx.eAff.map fun e =>
        (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e).length + 1).sum ≤
        uhTailHdr ∧
      ZeroFrom memReemb heapFin)
    (hjt_info : jtEList.Nodup ∧ jtEList.length = ctx.out.Jtilde.m ∧
      (∀ e, e ∈ jtEList ↔ e ∈ ctx.out.Jtilde.E))
    (hc_eqs : c.da.w = ctx.w ∧ c.vCap = ctx.vCap ∧ c.da.eCap = ctx.eCap ∧
      c.da.lo = ctx.j ∧ c.da.hi = ctx.L + 1 ∧ c.da.out = uhTailHdr + 1 ∧
      c.es = jtEList ∧ c.size ≤ 2 * ctx.oldBucketsSum + 4 * ctx.out.Jtilde.m)
    (hr_eqs : r.L = ctx.L ∧ r.vCap = ctx.vCap ∧ r.eCap = ctx.eCap ∧ r.b = ctx.b ∧ r.j = ctx.j ∧
      r.es = jtEList)
    (hPermRecs : (restrictUpdate ctx.u ctx.st.H ++ c.recs).Perm ctx.res.UH)
    (hApplyRecs : (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)).applyBatch c.recs =
      ctx.res.state.H)
    (hDelIns : ∀ u' ∈ c.recs, isDelOrIns u')
    (hminNew : ∀ e < ctx.eCap,
      (minHRebuild ctx.j jtEList.toFinset r.m0 e = 0 ↔ e ∉ ctx.res.state.H.E) ∧
      (e ∈ ctx.res.state.H.E → ∃ i : Fin (ctx.L + 1),
        minHRebuild ctx.j jtEList.toFinset r.m0 e = i.1 + 1 ∧
        e ∈ (ctx.res.state.H_level i).E ∧
        ∀ k' : Fin (ctx.L + 1), k'.1 < i.1 → e ∉ (ctx.res.state.H_level k').E))
    (hnewB : ∀ i : Fin (ctx.L + 1), ∀ e, e ∈ r.newB i.1 ↔
      e ∈ ctx.res.state.H.E ∧ minHRebuild ctx.j jtEList.toFinset r.m0 e = i.1 + 1)
    (hFinPost : (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
      uhTailHdr r ctx.G' ctx.eAff
      (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev) (fun _ => False)
      ctx.eAffPtr retSp heapFin).post
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
    (hFinPre_e : ∀ e ∈ ctx.eAff,
      retSp ≤ memReemb (retSp + e) ∧
      memReemb (retSp + e) + (mWalkEncode
        (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e)).length ≤ heapFin)
    (hGenEq : memGen = Function.update memFin (ctx.b + dsGenOff) (memFin (ctx.b + dsGenOff) + 1))
    (hdc_eqs : dc.w = ctx.w ∧ dc.eCap = ctx.eCap ∧ dc.T = ctx.embJH ∧ dc.es = jtEList ∧
      dc.esPtr = dgEListBase (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ∧
      dc.tab = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dc.stamp = dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      dc.g = memGen (ctx.b + dsGenOff) ∧ dc.out = dPtr ∧ dc.mem0 = memGen ∧
      dTotal ctx.embJH jtEList ≤ 2 * ctx.lenSum + ctx.eAff.length)
    (hColPost : (dsCollectDContract dc).post
      [dc.esPtr, dc.es.length, dc.tab, dc.stamp, dc.g, dc.out] memGen dLen memCol)
    (hFinalEq : memFinal = Function.update
      (Function.update (Function.update memCol ctx.heapStep uhTailHdr) (ctx.heapStep + 1) dPtr)
      (ctx.heapStep + 2) dLen) :
    StepPosMidPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.mem2 ctx.x ctx.headHeap ctx.r₁ ctx.heapStep ctx.heapAff ctx.sPrevList
      ctx.prefWords memFinal (dPtr + 2 * ctx.lenSum + ctx.eAff.length) ∧
    ListAt memFinal ctx.eAffPtr ctx.eAff ∧
    ctx.eAffPtr + ctx.eAff.length ≤ dPtr + 2 * ctx.lenSum + ctx.eAff.length := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hjle : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  obtain ⟨hgb_jt, hjt_sp, hlt_scr_ag⟩ := hSpInfo
  obtain ⟨hret_ge_hr, hret_le_hf, hSet_bnd, hZeroFin⟩ := hRe_bounds
  obtain ⟨hjt_nd, hjt_len, hjt_iff⟩ := hjt_info
  obtain ⟨hc_w, hc_v, hc_e, hc_lo, hc_hi, hc_out, hc_es, hc_size_le⟩ := hc_eqs
  obtain ⟨hr_L, hr_v, hr_e, hr_b, hr_j, hr_es⟩ := hr_eqs
  obtain ⟨hdc_w, hdc_e, hdc_T, hdc_es, _, _, hdc_st, hdc_g, hdc_out, _, hdTot⟩ := hdc_eqs
  obtain ⟨hG'_eq, hinDom_eq, hPi_eq, hD_eq⟩ := stepPosNE_res_eqs ctx hne hcanon
  have hHE_cap : ∀ e' ∈ ctx.res.state.H.E, e' < ctx.eCap := by
    have hL1 : 1 ≤ ctx.L := le_trans ctx.hj_pos hjle
    have hk1_inv := (step_inv ctx.hVG₀ hL1 ctx.hq ctx.hGm₀
      (canonicalSparsify_spec_absorb ctx.impl ctx.mMax) ctx.hBV ctx.hds ctx.hu_some ctx.hPref).1
    have hst1 : runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us (ctx.k + 1) =
        ctx.res.state := by
      simp only [runState, ctx.hu_some]
    have hsub : ctx.res.state.H.E ⊆ ctx.G'.E := by
      have h1 := hk1_inv.H_sub.2.1
      rw [← hk1_inv.G_eq, hst1, hG'_eq] at h1
      exact h1
    intro e' he'
    have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e' (E_applyUpdate_subset hdu.2 (hsub he'))
  have hGE'_cap : ∀ e' ∈ ctx.G'.E, e' < ctx.eCap := by
    intro e' he'
    have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e' (E_applyUpdate_subset hdu.2 he')
  rcases hFinPost with ⟨memMid, _, hTailPost, hSLWPost⟩
  rcases hTailPost with ⟨_, hDH_mid, hHdr_mid, hBB_mid, hBk_mid, hMin_mid, hDom0_mid, hS0_mid,
    hTailFr⟩
  rcases hSLWPost with ⟨eLP', mEP', hP', hSLW_args, hSLW_ge, hSLW_le, hGen_fin, hDomJ_fin,
    hVSt_fin, hEDom_fin, hEDom_iff, hPi_fin, ⟨revJ, hRev_fin⟩, hSLW_fr⟩
  have hSLW_eq : ctx.eAffPtr = eLP' ∧ retSp = mEP' ∧ heapFin = hP' := by
    simp only [List.cons.injEq] at hSLW_args
    exact ⟨hSLW_args.2.2.1, hSLW_args.2.2.2.2.1, hSLW_args.2.2.2.2.2.1⟩
  rcases hSLW_eq with ⟨rfl, rfl, rfl⟩
  rcases hColPost with ⟨hdLen_eq, hDList_col, hESt_col, hColFr⟩
  have hdList_le : (dList ctx.embJH jtEList).length ≤ dTotal ctx.embJH jtEList :=
    length_dList_le ctx.embJH jtEList
  have hcw_le : c.words ≤ c.size := by
    simp only [UTCtx.words, UTCtx.size, delList]
    have h1 := List.length_filter_le (fun e => decide (e ∉ c.da.X))
      (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))
    have h2 := insList_length_le c.Y c.es
    omega
  -- Bundle arithmetic bounds once via pure-ℕ helper so `omega` avoids context bloat
  let nextHeap := dPtr + 2 * ctx.lenSum + ctx.eAff.length
  have hAr_all :
      (ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.heapStep ∧
       ctx.heapStep + 5 ≤ ctx.heapAff ∧
       ctx.heapAff < ctx.scratchPtr ∧
       ctx.scratchPtr < retSp ∧
       retSp + ctx.eCap ≤ heapFin ∧
       heapFin ≤ retFin ∧
       retFin ≤ uhTailHdr ∧
       uhTailHdr + 1 + c.size ≤ dPtr ∧
       dPtr + dTotal ctx.embJH jtEList ≤ nextHeap) ∧
      (ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.heapStep ∧
       ctx.heapStep + 5 + ctx.prefWords ≤ ctx.headHeap ∧
       ctx.headHeap ≤ ctx.r₁ ∧ ctx.r₁ ≤ ctx.heapAff ∧
       ctx.heapAff + 2 + ctx.sPrevList.length ≤ ctx.scratchPtr ∧
       ctx.scratchPtr < retSp ∧
       retSp + ctx.eCap ≤ heapFin ∧
       heapFin ≤ retFin ∧
       retFin ≤ uhTailHdr ∧
       uhTailHdr + 1 + c.size ≤ dPtr ∧
       dPtr + dTotal ctx.embJH jtEList ≤ nextHeap) ∧
      (ctx.heapAff + 2 + ctx.sPrevList.length ≤ uhTailHdr ∧
       dPtr + dLen ≤ nextHeap ∧
       ctx.heapStep + 5 ≤ retSp ∧
       heapFin ≤ uhTailHdr ∧
       uhTailHdr ≤ nextHeap ∧
       0 < 1 + c.size ∧
       ctx.heapStep + 3 ≤ ctx.eAffPtr ∧
       ctx.eAffPtr + ctx.eAff.length ≤ ctx.scratchPtr ∧
       ctx.eAffPtr + ctx.eAff.length ≤ nextHeap) := by
    have h1 : ∀ (fix hs hh r1 ha pw spLen candLen eLen ls scr gb jtPtr dgSz retS ec retR
        hf rf sumSet hdr cSz obs jtm dp dt dl : ℕ),
        fix ≤ hs → hs + 5 + pw ≤ hh → hh ≤ r1 → r1 ≤ ha → 0 < eLen →
        ha + 2 + spLen + candLen + eLen + eLen + 14 * ls + 15 * eLen + candLen ≤ scr →
        scr < gb → gb ≤ jtPtr → jtPtr + dgSz ≤ retS →
        retS + ec ≤ retR → hf = retS + ec + 16 * eLen + 14 * ls + 3 * (retR - (retS + ec)) →
        hdr = hf + 2 * (retR - (retS + ec)) →
        hf ≤ rf → rf ≤ hf + sumSet → hf + sumSet ≤ hdr →
        cSz ≤ 2 * obs + 4 * jtm → dp = hdr + 1 + 2 * obs + 4 * jtm →
        dt ≤ 2 * ls + eLen → dl ≤ dt →
        (fix ≤ hs ∧ hs + 5 ≤ ha ∧ ha < scr ∧ scr < retS ∧ retS + ec ≤ hf ∧ hf ≤ rf ∧
          rf ≤ hdr ∧ hdr + 1 + cSz ≤ dp ∧ dp + dt ≤ dp + 2 * ls + eLen) ∧
        (fix ≤ hs ∧ hs + 5 + pw ≤ hh ∧ hh ≤ r1 ∧ r1 ≤ ha ∧ ha + 2 + spLen ≤ scr ∧
          scr < retS ∧ retS + ec ≤ hf ∧ hf ≤ rf ∧ rf ≤ hdr ∧ hdr + 1 + cSz ≤ dp ∧
          dp + dt ≤ dp + 2 * ls + eLen) ∧
        (ha + 2 + spLen ≤ hdr ∧ dp + dl ≤ dp + 2 * ls + eLen ∧ hs + 5 ≤ retS ∧ hf ≤ hdr ∧
          hdr ≤ dp + 2 * ls + eLen ∧ 0 < 1 + cSz ∧
          hs + 3 ≤ ha + 2 + spLen + candLen ∧
          ha + 2 + spLen + candLen + eLen ≤ scr ∧
          ha + 2 + spLen + candLen + eLen ≤ dp + 2 * ls + eLen) := by intros; omega
    have hdl_le_dt : dLen ≤ dTotal ctx.embJH jtEList := by
      rw [hdLen_eq, hdc_T, hdc_es]; exact hdList_le
    have hscr_lt_gb : ctx.scratchPtr < ctx.guestBase := by
      have := ctx.heAff_pos; dsimp only [StepPosNECtx.guestBase]; omega
    exact h1 (ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap) ctx.heapStep ctx.headHeap ctx.r₁
      ctx.heapAff ctx.prefWords ctx.sPrevList.length ctx.cand.length ctx.eAff.length ctx.lenSum
      ctx.scratchPtr ctx.guestBase (memSp ctx.scratchPtr) (dynGraphSize ctx.vCap ctx.eCap)
      retSp ctx.eCap retReemb heapFin retFin
      (2 * (ctx.eAff.map fun e =>
        (reembedWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.embMid ctx.S_prev e).length + 1).sum)
      uhTailHdr c.size ctx.oldBucketsSum ctx.out.Jtilde.m dPtr (dTotal ctx.embJH jtEList) dLen
      ctx.hfix_step ctx.hhead_in.1 ctx.hhead_in.2.1 ctx.hhead_in.2.2 ctx.heAff_pos
      (le_refl _) hscr_lt_gb hgb_jt hjt_sp hret_ge_hr hhf hhdr hSLW_ge hSLW_le hSet_bnd
      hc_size_le hdPtr hdTot hdl_le_dt
  obtain ⟨hAr_fr, hAr_c, hAr_extra⟩ := hAr_all
  -- Convert `hTailFr`, `hSLW_fr`, `hColFr` to `ctx` parameters for `stepPosNE_mid_frames`
  have hTailFr' : ∀ a, (a < uhTailHdr ∨ uhTailHdr + 1 + c.size ≤ a) →
      (a < dsHPtr ctx.b ctx.vCap ctx.eCap ∨ dsAuxPtr ctx.b ctx.vCap ctx.eCap ≤ a) →
      (a < dsMinHBase ctx.b ctx.vCap ctx.eCap ∨ dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a) →
      (a < dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.j + 1) ∨
        dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.L + 1) ≤ a) →
      (a < dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.j ∨
        dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.L + 1) ≤ a) →
      memMid a = memReemb a := fun a h1 h2 h3 h4 h5 =>
    hTailFr a (by rw [hc_out]; exact h1)
      (by rw [hr_b, hr_v, hr_e, hc_v, hc_e, hfl.2.2.1]; exact h2)
      (by rw [hr_b, hr_v, hr_e, hr_L]; exact h3)
      (not_genWord_of_outside hr_b hr_L hr_v hr_e hr_j h4 h5)
  have hSLW_fr' : ∀ a, dsLevelWalksFrameCond ctx.L ctx.vCap ctx.eCap ctx.b ctx.j heapFin retFin a →
      memFin a = memMid a := fun a ha =>
    hSLW_fr a (by rw [hr_L, hr_v, hr_e, hr_b, hr_j]; exact ha)
  have hColFr' : ∀ a, (a < dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap ∨
        dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.eCap ≤ a) →
      (a < dPtr ∨ dPtr + dTotal ctx.embJH jtEList ≤ a) → memCol a = memGen a := fun a h1 h2 =>
    hColFr a (by rw [hdc_st, hdc_e]; exact h1) (by rw [hdc_out, hdc_T, hdc_es]; exact h2)
  obtain ⟨hF_col, hF_fin, hF_mid_ltDom, hF_aff_ltH, hF_aff_aux, hF_aff_heap, hF_mem2_out,
    hF_mem0_dom, hF_mem2_S, hF_hdr0⟩ :=
    stepPosNE_mid_frames_a hjle hAr_fr ctx.hHdr_02 ctx.hDom_02 ctx.hAff_frame hlt_scr_ag hRe_lt
      hTailFr' hSLW_fr' hGenEq hColFr' hFinalEq
  obtain ⟨hF_uh, hZero_final, hgen_mid, hgen_final_step,
    hMid_retSp, hF_mid_domGt, hF_mid_sGe, hF_sBit, hG_eSt, hF_kept⟩ :=
    stepPosNE_mid_frames_b hjle hAr_fr ctx.hAff_frame hlt_scr_ag hRe_lt hZeroFin
      hTailFr' hSLW_fr' hGenEq hColFr' hF_col hF_fin
  obtain ⟨hF_stores, hF_dList, hF_G, hF_H, hF_aux, hF_bk, hF_minH, hF_domLt,
    ⟨hF_domJ, hF_edJ, hF_revJ, hF_piRange, hF_revRange⟩, hF_domGt, hF_Slt, hF_Svs,
    hF_vSt, hF_eSt, hF_headR, hF_prefR, hF_sPrevR⟩ :=
    stepPosNE_mid_frames_c hjle hAr_c ctx.hAff_frame hFinalEq hF_col hF_fin hF_mid_ltDom
      hF_aff_ltH hF_aff_aux hF_aff_heap hF_mem0_dom hF_mem2_S
  have hgen_fin' : memFin (ctx.b + dsGenOff) =
      ctx.memAff (ctx.b + dsGenOff) + 1 + ctx.eAff.length := by
    rw [hr_b] at hGen_fin; rw [hGen_fin, hgen_mid]
  have hgen_final : memFinal (ctx.b + dsGenOff) =
      ctx.memAff (ctx.b + dsGenOff) + 2 + ctx.eAff.length := by
    rw [hgen_final_step, hgen_fin']; omega
  have hgen_le_fin_final : memFin (ctx.b + dsGenOff) ≤ memFinal (ctx.b + dsGenOff) :=
    hgen_final_step ▸ Nat.le_succ _
  have hgen_aff_le_final : ctx.memAff (ctx.b + dsGenOff) ≤ memFinal (ctx.b + dsGenOff) := by
    rw [hgen_final]; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hgen_mem2_le_final : ctx.mem2 (ctx.b + dsGenOff) ≤ memFinal (ctx.b + dsGenOff) :=
    le_trans (ctx.hAff_gen ▸ Nat.le_succ _) hgen_aff_le_final
  have hgen_pos_final : 1 ≤ memFinal (ctx.b + dsGenOff) := by
    rw [hgen_final]; exact Nat.le_add_right_of_le (Nat.le_add_left 1 _)
  have hcardAff : ctx.eAff.length = ctx.E_aff.card := by
    rw [← List.toFinset_card_of_nodup ctx.hAff_eNd]
    congr 1
    ext e
    rw [List.mem_toFinset]
    exact ctx.hAff_iff e
  have hgen_upper_final :
      memFinal (ctx.b + dsGenOff) ≤ ctx.mem2 (ctx.b + dsGenOff) + 3 + ctx.E_aff.card := by
    rw [hgen_final, ctx.hAff_gen, ← hcardAff]
  have hAff_at_final : ListAt memFinal ctx.eAffPtr ctx.eAff :=
    listAt_of_agree (fun i hi =>
      hF_aff_heap (ctx.eAffPtr + i)
        (le_trans hAr_extra.2.2.2.2.2.2.1 (Nat.le_add_right _ _))
        (lt_of_lt_of_le (Nat.add_lt_add_left hi _) hAr_extra.2.2.2.2.2.2.2.1))
      ctx.hAff_at
  have hAff_le_final : ctx.eAffPtr + ctx.eAff.length ≤ nextHeap :=
    hAr_extra.2.2.2.2.2.2.2.2
  -- Clean up unused heavy hypotheses before building the final conjunction
  clear hSLW_args hgb_jt hjt_sp hret_ge_hr hret_le_hf hSet_bnd hZeroFin hSLW_ge hSLW_le
    hTailFr hSLW_fr hColFr hTailFr' hSLW_fr' hColFr' hhf hhdr hdPtr hne hcanon hfl hch hgo
    hAr_c hF_col hF_fin hF_mid_ltDom hF_aff_ltH hF_aff_aux hF_aff_heap hF_mem0_dom hF_mem2_S
  -- Assemble `StepPosMidPost` (zero `omega` calls)
  refine ⟨⟨uhTailHdr, dPtr, c, r, revJ, dList ctx.embJH jtEList,
    hF_stores.1, hF_stores.2.1, by rw [hF_stores.2.2, hdLen_eq, hdc_T, hdc_es],
    hAr_extra.1, hAr_fr.2.2.2.2.2.2.2.1, by rw [← hdc_es, ← hdc_T, ← hdLen_eq]; exact hAr_extra.2.1,
    hZero_final, ?_, ?_, hPermRecs, hDelIns,
    dList_nodup _ _, ?_, ?_, hr_L, hr_v, hr_e, hr_b, hr_j,
    ?_, ?_, ?_, ?_, ?_, hgen_pos_final, hgen_mem2_le_final, hgen_upper_final,
    ?_, ?_, ?_, ?_, ?_, ?_, hF_domLt, ?_, ?_, ?_, ?_, ?_, ?_, hF_prefR, ?_, ?_⟩,
    hAff_at_final, hAff_le_final⟩
  -- `memFinal uhTailHdr = c.recs.length`
  · rw [hF_uh uhTailHdr (le_refl _) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)),
      hHdr_mid]
  -- `∀ K, BatchBodyAt memFinal (uhTailHdr + 1) K c.recs c.words`
  · intro K
    refine (hc_out ▸ hBB_mid K).of_agree fun i hi =>
      hF_uh (uhTailHdr + 1 + i) (le_trans (Nat.le_succ _) (Nat.le_add_right _ _))
        (Nat.add_lt_add_left (lt_of_lt_of_le hi hcw_le) _)
  -- `(dList ctx.embJH jtEList).toFinset = ctx.res.D`
  · rw [dList_toFinset, hD_eq]
    have hset : jtEList.toFinset = ctx.out.Jtilde.E := by ext e; simp [hjt_iff]
    rw [hset]
  -- `ListAt memFinal dPtr (dList ctx.embJH jtEList)`
  · rw [hdc_out, hdc_T, hdc_es] at hDList_col
    exact listAt_of_agree (fun i _ => hF_dList i) hDList_col
  -- Header scalars `q, t, L, vCap, eCap`
  · rw [hF_hdr0 _ (by simp [dsQOff]) (by simp [dsQOff, dsGPtr, dsHdrSize]) (by simp [dsQOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr0 _ (by simp [dsTOff]) (by simp [dsTOff, dsGPtr, dsHdrSize]) (by simp [dsTOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr0 _ (by simp [dsLOff]) (by simp [dsLOff, dsGPtr, dsHdrSize]) (by simp [dsLOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr0 _ (by simp [dsVCapOff]) (by simp [dsVCapOff, dsGPtr, dsHdrSize]) (by simp [dsVCapOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr0 _ (by simp [dsECapOff]) (by simp [dsECapOff, dsGPtr, dsHdrSize]) (by simp [dsECapOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- `DynGraphAt` for `G`, `H`, `aux` and `BucketsAt`
  · rw [hG'_eq]; exact dynGraphAt_of_agree ctx.hG'_graph hF_G
  · rw [← hApplyRecs]; rw [hr_b, hr_v, hr_e, hc_v, hc_e] at hDH_mid
    exact dynGraphAt_of_agree hDH_mid hF_H
  · exact dynGraphAt_of_agree ctx.hAff_aux hF_aux
  · rw [hr_L, hr_v, hr_e, hr_b] at hBk_mid; exact hBk_mid.of_agree_range hF_bk
  -- `minH` postcondition
  · intro e he
    have hm := hMin_mid e (by rw [hr_e]; exact he)
    rw [hr_b, hr_v, hr_e, hr_j, hr_es] at hm
    rw [hF_minH e he, hm]; exact hminNew e he
  -- `r.newB` characterization
  · intro i e
    rw [hnewB i e]
    constructor
    · rintro ⟨heH, hmh⟩
      have he := hHE_cap e heH
      have hm := hMin_mid e (by rw [hr_e]; exact he)
      rw [hr_b, hr_v, hr_e, hr_j, hr_es] at hm
      exact ⟨heH, by rw [hF_minH e he, hm, hmh]⟩
    · rintro ⟨heH, hmh⟩
      have he := hHE_cap e heH
      have hm := hMin_mid e (by rw [hr_e]; exact he)
      rw [hr_b, hr_v, hr_e, hr_j, hr_es] at hm
      rw [hF_minH e he, hm] at hmh; exact ⟨heH, hmh⟩
  -- `∀ a, heapFoot ctx.x a → memFinal a = ctx.mem0 a`
  · intro a ha
    have halt : a < ctx.heapStep := ctx.hfoot_lt a ha
    rcases ha with ⟨iv, hiv, hlo, hhi⟩
    have hge : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ a :=
      le_trans (ctx.hState.2.2.1 iv hiv) hlo
    exact (hF_mem2_out a halt (Or.inr hge)).trans (ctx.hFoot_02 a ⟨iv, hiv, hlo, hhi⟩)
  -- Level `j`: domGen, edgeDomGen, Pi_level, revLists
  · rw [hr_b, hr_L, hr_v, hr_e, hr_j] at hDomJ_fin hEDom_fin hEDom_iff hPi_fin hRev_fin
    have hdomJ_val : memFinal (dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.j) =
        ctx.memAff (ctx.b + dsGenOff) + 1 := by rw [hF_domJ, hDomJ_fin, hgen_mid]
    refine ⟨by rw [hdomJ_val]; exact Nat.succ_pos _,
      by rw [hdomJ_val, hgen_final]; exact Nat.le_add_right_of_le (Nat.add_le_add_left (by decide) _),
      fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
    · rw [(hF_edJ e he).1, hF_domJ, hinDom_eq]
      exact ⟨le_trans (hEDom_fin e he) hgen_le_fin_final,
        (hEDom_iff e he).trans (ctx.hAff_iff e)⟩
    · have he_E : e ∈ ctx.E_aff := by rw [← hinDom_eq]; exact he
      have he_aff : e ∈ ctx.eAff := (ctx.hAff_iff e).mpr he_E
      have he_cap : e < ctx.eCap := hGE'_cap e (Finset.mem_filter.mp he_E).1
      obtain ⟨hpi_ptr, hpi_mw⟩ := hPi_fin e he_aff
      obtain ⟨hptr_ge, hptr_le⟩ := hFinPre_e e he_aff
      rw [hMid_retSp e he_cap] at hpi_ptr
      have hptr_eq : memFinal (dsPiPtrBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.j * ctx.eCap + e) =
          memReemb (retSp + e) := (hF_edJ e he_cap).2.trans hpi_ptr
      rw [hPi_eq]
      refine ⟨?_,
        by rw [hptr_eq]; exact le_trans hAr_extra.2.2.1 hptr_ge,
        by rw [hptr_eq]; exact le_trans hptr_le (le_trans hAr_extra.2.2.2.1 hAr_extra.2.2.2.2.1)⟩
      rw [(hF_edJ e he_cap).2]
      exact hpi_mw.of_agree fun a ha1 ha2 => by
        rw [hpi_ptr, Nat.add_assoc, ← mWalkEncode_length] at ha2
        rw [hpi_ptr] at ha1
        exact hF_piRange a (le_trans hptr_ge ha1)
          (lt_of_lt_of_le ha2 (le_trans hptr_le hAr_extra.2.2.2.1))
    · obtain ⟨hrg_le, hnd, hmem, hll⟩ := hRev_fin v hv
      refine ⟨by rw [(hF_revJ v hv).1]; exact le_trans hrg_le hgen_le_fin_final, hnd, ?_, ?_⟩
      · intro e; rw [hmem e, hApplyRecs, hG'_eq, hinDom_eq, hPi_eq, ctx.hAff_iff e]
      · rw [hF_domJ, (hF_revJ v hv).1, (hF_revJ v hv).2]
        split_ifs with hcond
        · simp only [hcond] at hll
          refine (hll.of_agree fun a ha => ?_).mono fun a ha => ?_
          · rcases ha with hf | ⟨h1, h2⟩
            · exact hf.elim
            · exact hF_piRange a (le_trans (le_trans (Nat.le_add_right _ _) hAr_fr.2.2.2.2.1) h1)
                (lt_of_lt_of_le h2 hAr_fr.2.2.2.2.2.2.1)
          · rcases ha with hf | ⟨h1, h2⟩
            · exact hf.elim
            · exact hF_revRange a h1 h2
        · simp only [hcond, ↓reduceIte] at hll; exact hll
  -- Levels `j < i`
  · intro i hi
    have hdom_i : memFinal (dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i.1) = 0 := by
      rw [hF_mid_domGt i.1 hi i.2]
      have h0 := hDom0_mid i.1 (by rw [hr_j]; exact hi) (by rw [hr_L]; exact i.2)
      rw [hr_b, hr_L, hr_v, hr_e] at h0; exact h0
    exact ⟨hdom_i, (hF_domGt i hi).1, (hF_domGt i hi).2⟩
  -- `S_level` storage
  · intro i
    split_ifs with hij
    · exact ⟨(hF_Slt i hij).1, (hF_Slt i hij).2.1, (hF_Slt i hij).2.2, hF_headR⟩
    · have hj_le_i : ctx.j ≤ i.1 := Nat.le_of_not_lt hij
      have hs0 : memFinal (dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i.1) = 0 := by
        rw [hF_mid_sGe i.1 hj_le_i i.2]
        have h0 := hS0_mid i.1 (by rw [hr_j]; exact hj_le_i) (by rw [hr_L]; exact i.2)
        rw [hr_b, hr_L, hr_v, hr_e] at h0; exact h0
      exact ⟨hs0, (hF_Svs i).1, (hF_Svs i).2⟩
  -- `sBit` and `vStamp`
  · intro v hv
    refine ⟨by rw [hF_sBit v hv]; exact ctx.hAff_sBit v hv, ?_⟩
    rw [hF_vSt v hv]
    rw [hr_b, hr_L, hr_v, hr_e] at hVSt_fin
    exact le_trans (hVSt_fin v hv) hgen_le_fin_final
  -- `eStamp` and `keptStamp`
  · intro e he
    refine ⟨?_, by rw [hF_kept e he]; exact ctx.hKept_02 e he⟩
    rw [hF_eSt e he]
    have hst := hESt_col e (by rw [hdc_e]; exact he)
    rw [hdc_st, hdc_T, hdc_es, hdc_g] at hst
    by_cases hmem : e ∈ dList ctx.embJH jtEList
    · rw [hst.1 hmem, hGenEq, Function.update_self, hgen_final_step]
    · rw [hst.2 hmem, hG_eSt e he]
      exact le_trans (ctx.hAff_eStamp e he) hgen_aff_le_final
  -- `ListAt memFinal (heapAff + 2) sPrevList`
  · exact listAt_of_agree hF_sPrevR ctx.hAff_sPrev
  -- `∀ a < heapStep, ¬ metaFoot b x a → memFinal a = mem0 a`
  · intro a ha hnm
    have hout : a < ctx.b ∨ ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ a := by
      by_contra h; push Not at h
      exact hnm (Or.inl ⟨h.1, by rw [ctx.hState.1, ctx.hState.2.1]; exact h.2⟩)
    exact (hF_mem2_out a ha hout).trans (ctx.hFrame_02 a ha hnm)

end MinCostFlow.DynSpanner.Program
