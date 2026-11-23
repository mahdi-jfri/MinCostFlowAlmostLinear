module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEmptyDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepAddr

/-!
# Glue for the empty branch of a `0 < j` step

When the affected set `E_aff` is empty, the step for `0 < j` needs no sparsification, no
re-embedding and no collection of `D`. The procedure `dsStepPosEmptyStmt`
(`DynSpannerStepPosEmptyDefs.lean`) only calls `dsStepFinishStmt` with an empty list of new
edges. This file holds the pure facts the proof of that procedure needs:

* `stepPosE_word_bounds`: the words the procedure computes fit in a machine word;
* `stepPosE_buildFinish`: the contexts and the precondition of the call to `dsStepFinishStmt`;
* `stepPosE_res_eqs`: the model's step keeps `G'`, leaves level `j` empty and has `D = ∅`.

The shared post `StepPosMidPost` is assembled in `DynSpannerStepPosEmptyPost.lean`, and the run
of the procedure is in `DynSpannerStepPosEmpty.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

lemma stepPosE_word_bounds (ctx : StepPosEmptyCtx) :
    ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap < 2 ^ ctx.w ∧
    ctx.b < 2 ^ ctx.w ∧ ctx.j + 1 < 2 ^ ctx.w ∧ ctx.L + 1 < 2 ^ ctx.w ∧
    ctx.vCap < 2 ^ ctx.w ∧ ctx.eCap < 2 ^ ctx.w ∧
    ctx.eAffPtr < 2 ^ ctx.w ∧ ctx.retAff < 2 ^ ctx.w ∧
    ctx.uhTailHdr + 1 < 2 ^ ctx.w ∧ ctx.dPtr < 2 ^ ctx.w ∧
    2 * ctx.oldBucketsSum < 2 ^ ctx.w ∧ ctx.heapStep + 2 < 2 ^ ctx.w ∧
    16 < 2 ^ ctx.w := by
  have hj_le : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hb1 : 1 ≤ ctx.b := ctx.hState.2.2.2.1
  have h1 : ∀ (b L vc ec j hs pw hh r1 ha ra sp cl obs tw : ℕ),
      1 ≤ b → j ≤ L →
      b + dsFixedSize L vc ec ≤ hs →
      hs + 5 + pw ≤ hh → hh ≤ r1 → r1 ≤ ha → ha + 2 + sp + cl ≤ ra →
      ra + ec + 1 + 2 * obs < tw →
      b + dsFixedSize L vc ec < tw ∧ b < tw ∧ j + 1 < tw ∧ L + 1 < tw ∧
      vc < tw ∧ ec < tw ∧ ha + 2 + sp + cl < tw ∧ ra < tw ∧
      ra + ec + 1 < tw ∧ ra + ec + 1 + 2 * obs < tw ∧ 2 * obs < tw ∧
      hs + 2 < tw ∧ 16 < tw := by
    intro b L vc ec j hs pw hh r1 ha ra sp cl obs tw hb1 hj hfx h1 h2 h3 h4 hlt
    have hfl := fixed_layout_order b L vc ec
    have hdg : 4 + 7 * vc + 9 * ec = dynGraphSize vc ec := rfl
    have hL1 : dsDomGenBase b L vc ec + (L + 1) ≤ b + dsFixedSize L vc ec := by omega
    have hdg_le : b + dsHdrSize + 3 * dynGraphSize vc ec ≤ b + dsFixedSize L vc ec := by omega
    have hhdr : dsHdrSize = 6 := rfl
    omega
  exact h1 ctx.b ctx.L ctx.vCap ctx.eCap ctx.j ctx.heapStep ctx.prefWords ctx.headHeap ctx.r₁
    ctx.heapAff ctx.retAff ctx.sPrevList.length ctx.cand.length ctx.oldBucketsSum (2 ^ ctx.w)
    hb1 hj_le ctx.hfix_step ctx.hhead_in.1 ctx.hhead_in.2.1 ctx.hhead_in.2.2 ctx.hret_ge
    ctx.hEnd_ltw

/-! ## Pure glue lemmas for the `E_aff = ∅` branch -/

/-- An address outside the words that `dsSetLevelWalksStmt` writes at level `lvl`: below the
`domGen` words, between the `sGen` and the `vStamp` words, or after the fixed block. -/
lemma lwFrame_of {L vCap eCap b lvl hp ret a : ℕ} (hl : lvl ≤ L) (hgen : a ≠ b + dsGenOff)
    (hreg : a < dsDomGenBase b L vCap eCap ∨
      (dsSGenBase b L vCap eCap ≤ a ∧ a < dsVStampBase b L vCap eCap) ∨
      b + dsFixedSize L vCap eCap ≤ a)
    (hr : a < hp ∨ ret ≤ a) : dsLevelWalksFrameCond L vCap eCap b lvl hp ret a := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    fixed_layout_order b L vCap eCap
  have hlt : lvl < L + 1 := Nat.lt_succ_of_le hl
  refine ⟨hgen, by omega, fun e he => ?_, fun e he => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v hv => by omega, hr⟩
  · have := idx_lt_rows hlt he; omega
  · have := idx_lt_rows hlt he; omega
  · have := idx_lt_rows hlt hv; omega
  · have := idx_lt_rows hlt hv; omega


lemma stepPosE_buildFinish (ctx : StepPosEmptyCtx) :
    ∃ (c : UTCtx) (r : RBCtx),
      c.da.w = ctx.w ∧ c.da.eCap = ctx.eCap ∧ c.vCap = ctx.vCap ∧ c.da.lo = ctx.j ∧
      c.da.hi = ctx.L + 1 ∧ c.da.out = ctx.uhTailHdr + 1 ∧ c.es = [] ∧
      c.size = 2 * ctx.oldBucketsSum ∧
      (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length = ctx.oldBucketsSum ∧
      r.L = ctx.L ∧ r.vCap = ctx.vCap ∧ r.eCap = ctx.eCap ∧ r.b = ctx.b ∧ r.j = ctx.j ∧
      r.es = [] ∧ (bucketsCat r.B r.j (r.L + 1 - r.j)).length = ctx.oldBucketsSum ∧
      (restrictUpdate ctx.u ctx.st.H ++ c.recs).Perm ctx.res.UH ∧
      (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)).applyBatch c.recs = ctx.res.state.H ∧
      (∀ u' ∈ c.recs, isDelOrIns u') ∧
      (∀ e < ctx.eCap,
        (minHRebuild ctx.j ∅ r.m0 e = 0 ↔ e ∉ ctx.res.state.H.E) ∧
        (e ∈ ctx.res.state.H.E → ∃ i : Fin (ctx.L + 1),
          minHRebuild ctx.j ∅ r.m0 e = i.1 + 1 ∧
          e ∈ (ctx.res.state.H_level i).E ∧
          ∀ k' : Fin (ctx.L + 1), k'.1 < i.1 → e ∉ (ctx.res.state.H_level k').E)) ∧
      (∀ i : Fin (ctx.L + 1), ∀ e, e ∈ r.newB i.1 ↔
        e ∈ ctx.res.state.H.E ∧ minHRebuild ctx.j ∅ r.m0 e = i.1 + 1) ∧
      (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
        ctx.uhTailHdr r ctx.G' [] (fun _ => []) (fun _ => False)
        ctx.eAffPtr ctx.retAff ctx.uhTailHdr).pre
        ([dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          ctx.retAff, ctx.uhTailHdr + 1, ctx.retAff, 0,
          dgEPresBase (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap,
          dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, ctx.uhTailHdr] ++
         [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b, ctx.retAff, 0] ++
         [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
          ctx.j + 1, ctx.j, ctx.L + 1] ++
         [ctx.b, ctx.j, ctx.eAffPtr, 0, ctx.retAff, ctx.uhTailHdr]) ctx.memAff := by
  have hEA : ctx.eAffPtr = ctx.heapAff + 2 + ctx.sPrevList.length + ctx.cand.length := rfl
  have hUH : ctx.uhTailHdr = ctx.retAff + ctx.eCap := rfl
  have hDP : ctx.dPtr = ctx.retAff + ctx.eCap + 1 + 2 * ctx.oldBucketsSum := rfl
  have hOff : dsQOff = 0 ∧ dsTOff = 1 ∧ dsLOff = 2 ∧ dsVCapOff = 3 ∧ dsECapOff = 4 ∧
      dsGenOff = 5 ∧ dsHdrSize = 6 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hhi1, hhi2, hhi3⟩ := ctx.hhead_in
  have hfs := ctx.hfix_step
  have hrg := ctx.hret_ge
  have hel := ctx.hEnd_ltw
  have hgl := ctx.hGen_ltw
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hwb := stepPosE_word_bounds ctx
  have hj_le : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hfix_ret : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.retAff := by
    have := ctx.hfix_step; have := ctx.hhead_in; have := ctx.hret_ge; omega
  have hfix_eAff : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.eAffPtr := by
    have := ctx.hfix_step; have := ctx.hhead_in; omega
  have hag_hdr : ∀ addr, ctx.b ≤ addr → addr < dsGPtr ctx.b → addr ≠ ctx.b + dsGenOff →
      ctx.memAff addr = ctx.mem0 addr := fun addr h1 h2 hne =>
    (ctx.hAff_frame addr (by have := ctx.hfix_step; have := ctx.hhead_in; omega) hne
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      (ctx.hHdr_02 addr h1 h2 hne)
  have hag_buck : ∀ addr, dsMinHBase ctx.b ctx.vCap ctx.eCap ≤ addr →
      addr < dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap → ctx.memAff addr = ctx.mem2 addr :=
    fun addr h1 h2 =>
      ctx.hAff_frame addr (by have := ctx.hfix_step; have := ctx.hhead_in; omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have hDG' : DynGraphAt ctx.memAff (dsGPtr ctx.b) ctx.vCap ctx.eCap ctx.G' :=
    dynGraphAt_of_agree ctx.hG'_graph fun a h1 h2 =>
      ctx.hAff_frame a (by have := ctx.hfix_step; have := ctx.hhead_in; omega) (by omega)
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have hDHmid : DynGraphAt ctx.memAff (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap ctx.eCap
      (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)) :=
    dynGraphAt_of_agree ctx.hHmid_graph fun a h1 h2 =>
      ctx.hAff_frame a (by have := ctx.hfix_step; have := ctx.hhead_in; omega) (by omega)
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have hjt_iff :
      let st := ctx.st
      let j := ctx.j
      let G' := ctx.G'
      let H_mid : Fin (ctx.L + 1) → MGraph :=
        fun i => (st.H_level i).applyBatch (restrictUpdate ctx.u (st.H_level i))
      let inDom_mid : Fin (ctx.L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
      let S_prev := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G ctx.u
      let H_lt := unionGraphLt G' H_mid j
      let piLt_mid := piLtFrom st.Pi_level inDom_mid j
      let E_aff := affectedEdges G' H_lt piLt_mid S_prev
      let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
      let H_aux := buildAuxHost G' H_lt E_aff
      let embJH := projWalk G' H_lt piLt_mid S_prev
      let out := if E_aff.Nonempty then canonicalSparsify ctx.impl H_aux J embJH else ⟨J, idEmb, 0⟩
      ∀ e, e ∈ ([] : List ℕ) ↔ e ∈ out.Jtilde.E := by
    dsimp only
    intro e
    have hE : affectedEdges ctx.G'
        (unionGraphLt ctx.G' (fun i => (ctx.st.H_level i).applyBatch (restrictUpdate ctx.u (ctx.st.H_level i))) ctx.j)
        (piLtFrom ctx.st.Pi_level (fun i => ctx.st.inDom i ∩ ctx.G'.E) ctx.j)
        (ctx.st.S_level ⟨ctx.j - 1, by omega⟩ ∪ touchedVertices ctx.st.G ctx.u) = ∅ := ctx.hAff_empty
    simp [buildProjGraph, hE]
  have hjt_pres : ∀ e < ctx.eCap, ctx.memAff (ctx.retAff + e) = if e ∈ ([] : List ℕ).toFinset then 1 else 0 := by
    intro e _
    simp only [List.toFinset_nil, Finset.notMem_empty, ↓reduceIte]
    exact ctx.hZeroAff _ (Nat.le_add_right _ _)
  have hsz_w :
      let Bmid := fun i => delErase ctx.u (if hi : i < ctx.L + 1 then ctx.x.hBuckets ⟨i, hi⟩ else [])
      ctx.uhTailHdr + 1 + (2 * (bucketsCat Bmid ctx.j (ctx.L + 1 - ctx.j)).length + 4 * ([] : List ℕ).length) <
        2 ^ ctx.w := by
    dsimp only; rw [← ctx.hOldSum]; simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    exact ctx.hEnd_ltw
  obtain ⟨c, r, hc_w, hc_e, hc_v, hc_m0, hc_n, hc_h, hc_l, hc_lo, hc_hi, hc_pr, hc_out, hc_B,
    hc_esP, hc_es, hc_pY, hc_gP, hr_w, hr_L, hr_v, hr_e, hr_b, hr_j, hr_es, hr_esP, hr_B, hr_m0,
    hTailPre, hApplyRecs, hPermRecs, hDelIns, _, hminNew, hnewB⟩ :=
    buildFinishCtx ctx.hVG₀ ctx.hq ctx.hGm₀ ctx.hBV ctx.hds ctx.hu_some ctx.hPref ctx.hj_pos
      ctx.hw16 ctx.hState ctx.hGV'_cap hwb.1 (by omega) ctx.hBk_mem2 ctx.hmin2 hag_hdr hag_buck
      hDG' hDHmid List.nodup_nil hjt_iff (fun k hk => (Nat.not_lt_zero _ hk).elim) hjt_pres
      hfix_ret (by simp [StepPosEmptyCtx.uhTailHdr]) (by simp [StepPosEmptyCtx.uhTailHdr]) hsz_w
  have hbc : (bucketsCat (fun i => delErase ctx.u (if hi : i < ctx.L + 1 then ctx.x.hBuckets ⟨i, hi⟩ else []))
      ctx.j (ctx.L + 1 - ctx.j)).length = ctx.oldBucketsSum := ctx.hOldSum.symm
  have hc_size : c.size = 2 * ctx.oldBucketsSum := by
    show 2 * (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo)).length + 4 * c.es.length = _
    rw [hc_B, hc_lo, hc_hi, hc_es, hbc]; simp
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hG'val : ctx.G'.IsValid :=
    isValid_applyUpdate_of_delOrSplit ctx.hState.2.2.2.2.1
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hdu.1) hdu.2
  have hGE'_cap : ∀ e ∈ ctx.G'.E, e < ctx.eCap := fun e he =>
    ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu.2 he)
  have hnext := step_inv ctx.hVG₀ (le_trans ctx.hj_pos hj_le) ctx.hq ctx.hGm₀
    (canonicalSparsify_spec_absorb ctx.impl ctx.mMax) ctx.hBV ctx.hds ctx.hu_some ctx.hPref
  have hst1 : runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us (ctx.k + 1) =
      ctx.res.state := by simp [StepPosEmptyCtx.res, StepPosEmptyCtx.st, runState, ctx.hu_some]
  have hresG : ctx.res.state.G = ctx.G' := by
    have hk := ctx.hPref ctx.k (le_refl _)
    have hjne : chooseLevel ctx.L ctx.q (ctx.k + 1) ≠ 0 := Nat.ne_of_gt ctx.hj_pos
    simp [StepPosEmptyCtx.res, step, hk.t_eq, hk.q_eq, hjne]
  have hH'val : ctx.res.state.H.IsValid := by rw [← hst1]; exact hnext.1.H_valid
  have hH'V : ctx.res.state.H.V = ctx.G'.V := by
    have h1 := hnext.1.H_V; rw [hst1, ← hnext.1.G_eq, hst1, hresG] at h1; exact h1
  have hH'E_sub : ctx.res.state.H.E ⊆ ctx.G'.E := by
    have h1 := hnext.1.H_sub; rw [hst1, ← hnext.1.G_eq, hst1, hresG] at h1; exact h1.2.1
  have hDom0 := ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdom_ag : ∀ a, dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a →
      a < dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap → ctx.memAff a = ctx.mem0 a := fun a h1 h2 =>
    (ctx.hAff_frame a (by have := ctx.hfix_step; have := ctx.hhead_in; omega) (by omega)
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      (ctx.hDom_02 a h1 h2)
  have hgen_0aff : ctx.mem0 (ctx.b + dsGenOff) ≤ ctx.memAff (ctx.b + dsGenOff) := by
    have := ctx.hgen_02; have := ctx.hAff_gen; omega
  refine ⟨c, r, hc_w, hc_e, hc_v, hc_lo, hc_hi, hc_out, hc_es, hc_size,
    by rw [hc_B, hc_lo, hc_hi]; exact hbc, hr_L, hr_v, hr_e, hr_b, hr_j, hr_es,
    by rw [hr_B, hr_L, hr_j]; exact hbc, hPermRecs, hApplyRecs, hDelIns,
    by simpa using hminNew, by simpa using hnewB, ?_⟩
  refine ⟨?_, ?_, by rw [hc_v, hr_v], by rw [hc_e, hr_e],
    by rw [hr_b]; exact ctx.hState.2.2.2.1, by rw [hr_b, hr_L, hr_v, hr_e]; omega, le_refl _,
    by rw [hc_w]; simpa using Nat.lt_of_succ_lt hwb.2.2.2.2.2.2.2.2.1,
    by rw [hr_b, hr_L, hr_v, hr_e]; exact hfix_eAff,
    by simp only [List.length_nil, Nat.add_zero] <;> omega,
    by rw [hr_b, hr_L, hr_v, hr_e]; exact hfix_ret, by rw [hr_e],
    by rw [hr_b, hc_w]; simp only [List.length_nil, Nat.add_zero]; omega,
    fun v hv => by
      rw [hr_v] at hv
      rw [hr_b, hr_L, hr_v, hr_e]
      rw [ctx.hAff_frame _ (by have := ctx.hfix_step; have := ctx.hhead_in; omega) (by omega)
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      have := ctx.hVSt_02 v hv; have := ctx.hAff_gen; omega,
    fun e he => by
      rw [hr_e] at he
      rw [hr_b, hr_L, hr_v, hr_e, hr_j]
      have hm : ctx.j * ctx.eCap + e < (ctx.L + 1) * ctx.eCap := by
        calc ctx.j * ctx.eCap + e < ctx.j * ctx.eCap + ctx.eCap := Nat.add_lt_add_left he _
          _ = (ctx.j + 1) * ctx.eCap := by ring
          _ ≤ (ctx.L + 1) * ctx.eCap := Nat.mul_le_mul_right _ (by omega)
      have hm' : chooseLevel ctx.L ctx.q (ctx.k + 1) * ctx.eCap + e < (ctx.L + 1) * ctx.eCap := hm
      rw [hdom_ag _ (by omega) (by omega)]
      exact le_trans ((hDom0 ⟨ctx.j, by omega⟩).2.1 e he).1 hgen_0aff,
    fun v hv => by
      rw [hr_v] at hv
      rw [hr_b, hr_L, hr_v, hr_e, hr_j]
      have hm : ctx.j * ctx.vCap + v < (ctx.L + 1) * ctx.vCap := by
        calc ctx.j * ctx.vCap + v < ctx.j * ctx.vCap + ctx.vCap := Nat.add_lt_add_left hv _
          _ = (ctx.j + 1) * ctx.vCap := by ring
          _ ≤ (ctx.L + 1) * ctx.vCap := Nat.mul_le_mul_right _ (by omega)
      have hm' : chooseLevel ctx.L ctx.q (ctx.k + 1) * ctx.vCap + v < (ctx.L + 1) * ctx.vCap := hm
      rw [hdom_ag _ (by omega) (by omega)]
      exact le_trans ((hDom0 ⟨ctx.j, by omega⟩).2.2.2.2.2 v hv).1 hgen_0aff,
    fun _ h => h.elim, List.nodup_nil, fun k hk => (Nat.not_lt_zero _ hk).elim,
    by rw [hr_b, hr_v, hr_e]; exact hDG', hG'val,
    fun v hv => by rw [hr_v]; exact ctx.hGV'_cap v hv,
    fun e he => by rw [hr_e]; exact hGE'_cap e he,
    by rw [hApplyRecs]; exact hH'val,
    by rw [hApplyRecs, hH'V],
    fun v hv => by rw [hr_v]; rw [hApplyRecs, hH'V] at hv; exact ctx.hGV'_cap v hv,
    fun e he => by rw [hr_e]; rw [hApplyRecs] at he; exact hGE'_cap e (hH'E_sub he),
    fun _ h => (List.not_mem_nil h).elim⟩
  · rw [hr_b, hr_v, hr_e]; exact hTailPre
  · rw [hr_b, hr_j]; rfl

/-- When `E_aff = ∅`, the step keeps `G'`, leaves level `j` with an empty domain, and adds no
edge to `D`. -/
lemma stepPosE_res_eqs (ctx : StepPosEmptyCtx) :
    let jF : Fin (ctx.L + 1) := ⟨ctx.j, Nat.lt_succ_of_le (chooseLevel_le ctx.L ctx.q (ctx.k + 1))⟩
    ctx.res.state.G = ctx.G' ∧ ctx.res.state.inDom jF = ∅ ∧ ctx.res.D = ∅ := by
  have hE := ctx.hAff_empty
  dsimp only at hE
  have hk := ctx.hPref ctx.k (le_refl _)
  have ht : ctx.st.t = ctx.k := hk.t_eq
  have hq : ctx.st.q = ctx.q := hk.q_eq
  have hjne : chooseLevel ctx.L ctx.q (ctx.k + 1) ≠ 0 := Nat.ne_of_gt ctx.hj_pos
  have hstep : ctx.res = step ctx.st ctx.u (canonicalSparsify ctx.impl) := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [hstep, step, ht, hq, hjne, ↓reduceDIte]
  · simp only [hstep, step, ht, hq, hjne, ↓reduceDIte, lt_irrefl, ↓reduceIte]
    exact hE
  · simp only [hstep, step, ht, hq, hjne, ↓reduceDIte]
    simp [hE, buildProjGraph]

end

end MinCostFlow.DynSpanner.Program
