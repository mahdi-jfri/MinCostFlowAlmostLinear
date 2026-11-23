module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEpilogueDefs
import MinCostFlow.DynSpanner.Program.DynSpannerStepAddr

/-!
# Common epilogue of a `0 < j` step: from the memory to `StepOutPost`

The epilogue `dsStepPosEpilogueStmt` changes only a few ranges of memory: the word `t`, the graph
`aux`, the `sBit` words, the step header at `heapStep`, and the new batch `U_H` from `nextHeap`
on. This file proves `stepPosEp_post`: if a memory agrees with the memory before the epilogue
outside these ranges and holds the right words inside them, then it satisfies `StepOutPost`. The
new state is rebuilt by `rebuildStatePos` (`DynSpannerStepPosJoinB.lean`). The run of the epilogue
itself is in `DynSpannerStepPosEpilogue.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

private lemma le_chain_uh {a b c d e : ℕ} (h1 : a + 1 + b ≤ c) (h2 : c + d ≤ e) : a ≤ e := by
  omega

private lemma hdrWord_lt_aux {b vCap eCap off : ℕ} (h : off < dsHdrSize) :
    b + off < dsAuxPtr b vCap eCap := by
  simp only [dsAuxPtr, dsHPtr, dsGPtr]
  omega

private lemma hdrWord_ne_t {b off : ℕ} (h : off ≠ dsTOff) : b + off ≠ b + dsTOff := by
  omega

private lemma graph_word_ok {b vCap eCap a p : ℕ}
    (hp : p = dsGPtr b ∨ p = dsHPtr b vCap eCap) (h1 : p ≤ a)
    (h2 : a < p + dynGraphSize vCap eCap) :
    b ≤ a ∧ a < dsAuxPtr b vCap eCap ∧ a ≠ b + dsTOff := by
  simp only [dsAuxPtr, dsHPtr, dsGPtr, dsTOff, dsHdrSize] at hp h1 h2 ⊢
  omega

public section

/-- The memory after the epilogue satisfies `StepOutPost`, given that it agrees with the memory
`ctx.memMid` before the epilogue outside the ranges the epilogue writes, and holds the new words
inside them: `t + 1`, the empty graph `aux`, zero `sBit` words, the step header, and the batch
`restrictUpdate u H ++ c.recs` at `nextHeap`. -/
theorem stepPosEp_post (ctx : StepPosEpCtx) {uhTailHdr dPtr : ℕ} {c : UTCtx} {r : RBCtx}
    {revJ : ℕ → List ℕ} {dL : List ℕ}
    (hB : StepPosMidBody ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.mem2 ctx.x ctx.headHeap ctx.r₁ ctx.heapStep ctx.heapAff ctx.sPrevList
      ctx.prefWords ctx.memMid ctx.nextHeap uhTailHdr dPtr c r revJ dL)
    {memFinal : ℕ → ℕ} {uhWords : ℕ}
    (hF_low : ∀ a < ctx.b, memFinal a = ctx.memMid a)
    (hF_hdr : ∀ a, ctx.b ≤ a → a < dsAuxPtr ctx.b ctx.vCap ctx.eCap → a ≠ ctx.b + dsTOff →
      memFinal a = ctx.memMid a)
    (hF_arr : ∀ a, dsMinHBase ctx.b ctx.vCap ctx.eCap ≤ a →
      a < dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap → memFinal a = ctx.memMid a)
    (hF_arr2 : ∀ a, dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.vCap ≤ a → a < ctx.heapStep →
      memFinal a = ctx.memMid a)
    (hF_heap : ∀ a, ctx.heapStep + 5 ≤ a → a < ctx.nextHeap → memFinal a = ctx.memMid a)
    (hF_t : memFinal (ctx.b + dsTOff) = ctx.st.t + 1)
    (hF_aux : DynGraphAt memFinal (dsAuxPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap ctx.eCap
      emptyMGraph)
    (hF_sb : ∀ v < ctx.vCap, memFinal (dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap + v) = 0)
    (hF_h0 : memFinal ctx.heapStep = ctx.nextHeap)
    (hF_h1 : memFinal (ctx.heapStep + 1) = (restrictUpdate ctx.u ctx.st.H ++ c.recs).length)
    (hF_h2 : memFinal (ctx.heapStep + 2) = uhWords)
    (hF_h3 : memFinal (ctx.heapStep + 3) = dPtr)
    (hF_h4 : memFinal (ctx.heapStep + 4) = dL.length)
    (hF_uh : BatchBodyAt memFinal ctx.nextHeap ctx.st.H (restrictUpdate ctx.u ctx.st.H ++ c.recs)
      uhWords)
    (hF_zero : ZeroFrom memFinal (ctx.nextHeap + uhWords)) :
    StepOutPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.x ctx.heapStep memFinal (ctx.nextHeap + uhWords) := by
  obtain ⟨hM_hdr0, hM_hdr1, hM_hdr2, hM_aff_uh, hM_uh_d, hM_d_nh, hM_zero,
    hM_cnt, hM_body, hM_perm, hM_delIns, hM_dNd, hM_dFin, hM_dAt,
    hr_L, hr_v, hr_e, hr_b, hr_j,
    hM_q, hM_t, hM_L, hM_vC, hM_eC, hM_gen1, hM_gen2, hM_gen3,
    hM_G, hM_H, hM_Aux, hM_Bk, hM_minH, hM_newB,
    hM_domLt, hM_foot0, hM_lvlJ, hM_domGt, hM_S, hM_sbVst, hM_eKept,
    hM_prefAg, hM_sPrevAt, hM_frame0⟩ := hB
  have hj_le : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hj_pos : 0 < ctx.j := ctx.hj_pos
  -- The order of the pointers of the step.
  have hHS : ctx.heapStep + 5 ≤ ctx.headHeap := le_trans (Nat.le_add_right _ _) ctx.hhead_in.1
  have hr1 : ctx.r₁ ≤ uhTailHdr :=
    le_trans ctx.hhead_in.2.2 (le_trans (Nat.le_add_right _ _)
      (le_trans (Nat.le_add_right _ _) hM_aff_uh))
  have hdP : ctx.heapStep + 5 ≤ dPtr :=
    le_trans hHS (le_trans ctx.hhead_in.2.1 (le_trans hr1 (le_trans (Nat.le_add_right _ _)
      (le_trans (Nat.le_add_right _ _) hM_uh_d))))
  have hnh : ctx.nextHeap ≤ ctx.nextHeap + uhWords := Nat.le_add_right _ _
  have hU_n : uhTailHdr ≤ ctx.nextHeap := le_chain_uh hM_uh_d hM_d_nh
  have hfix : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.heapStep := ctx.hfix_step
  have hsb := sBit_in_block ctx.b ctx.L ctx.vCap ctx.eCap
  -- Frames by region.
  have hK_hdr : ∀ off, off < dsHdrSize → off ≠ dsTOff →
      memFinal (ctx.b + off) = ctx.memMid (ctx.b + off) := fun off h1 h2 =>
    hF_hdr _ (Nat.le_add_right _ _) (hdrWord_lt_aux h1) (hdrWord_ne_t h2)
  have hK_graph : ∀ p, (p = dsGPtr ctx.b ∨ p = dsHPtr ctx.b ctx.vCap ctx.eCap) →
      ∀ a, p ≤ a → a < p + dynGraphSize ctx.vCap ctx.eCap → memFinal a = ctx.memMid a :=
    fun p hp a h1 h2 =>
      have h := graph_word_ok hp h1 h2
      hF_hdr a h.1 h.2.1 h.2.2
  have hK_e : ∀ i ≤ ctx.L, ∀ e < ctx.eCap,
      memFinal (dsEdgeDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.eCap + e) =
        ctx.memMid (dsEdgeDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.eCap + e) ∧
      memFinal (dsPiPtrBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.eCap + e) =
        ctx.memMid (dsPiPtrBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.eCap + e) :=
    fun i hi e he =>
      have h := edgeWord_in_levels (vCap := ctx.vCap) (b := ctx.b) hi he
      ⟨hF_arr _ h.1.1 h.1.2, hF_arr _ h.2.1 h.2.2⟩
  have hK_v : ∀ i ≤ ctx.L, ∀ v < ctx.vCap,
      memFinal (dsRevGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.vCap + v) =
        ctx.memMid (dsRevGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.vCap + v) ∧
      memFinal (dsRevHeadBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.vCap + v) =
        ctx.memMid (dsRevHeadBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.vCap + v) ∧
      memFinal (dsVSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.vCap + v) =
        ctx.memMid (dsVSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i * ctx.vCap + v) :=
    fun i hi v hv =>
      have h := vertexWord_in_levels (eCap := ctx.eCap) (b := ctx.b) hi hv
      ⟨hF_arr _ h.1.1 h.1.2, hF_arr _ h.2.1.1 h.2.1.2, hF_arr _ h.2.2.1 h.2.2.2⟩
  have hK_i : ∀ i ≤ ctx.L,
      memFinal (dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i) =
        ctx.memMid (dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i) ∧
      memFinal (dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i) =
        ctx.memMid (dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i) ∧
      memFinal (dsSHeadBase ctx.b ctx.L ctx.vCap ctx.eCap + i) =
        ctx.memMid (dsSHeadBase ctx.b ctx.L ctx.vCap ctx.eCap + i) :=
    fun i hi =>
      have h := levelWord_in_levels (vCap := ctx.vCap) (eCap := ctx.eCap) (b := ctx.b) hi
      ⟨hF_arr _ h.1.1 h.1.2, hF_arr _ h.2.1.1 h.2.1.2, hF_arr _ h.2.2.1 h.2.2.2⟩
  have hK_minH : ∀ e < ctx.eCap, memFinal (dsMinHBase ctx.b ctx.vCap ctx.eCap + e) =
      ctx.memMid (dsMinHBase ctx.b ctx.vCap ctx.eCap + e) := fun e he =>
    have h := minH_in_levels (L := ctx.L) (b := ctx.b) (vCap := ctx.vCap) he
    hF_arr _ h.1 h.2
  have hK_vst : ∀ v < ctx.vCap,
      memFinal (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) =
        ctx.memMid (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) := fun v hv =>
    have h := vStampWord_in_block (b := ctx.b) (L := ctx.L) (eCap := ctx.eCap) hv
    hF_arr2 _ h.1 (lt_of_lt_of_le h.2 hfix)
  have hK_est : ∀ e < ctx.eCap,
      memFinal (dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + e) =
        ctx.memMid (dsEStampBase ctx.b ctx.L ctx.vCap ctx.eCap + e) ∧
      memFinal (dsKeptStampBase ctx.b ctx.L ctx.vCap ctx.eCap + e) =
        ctx.memMid (dsKeptStampBase ctx.b ctx.L ctx.vCap ctx.eCap + e) := fun e he =>
    have h := eStampWord_in_block (b := ctx.b) (L := ctx.L) (vCap := ctx.vCap) he
    ⟨hF_arr2 _ h.1.1 (lt_of_lt_of_le h.1.2 hfix), hF_arr2 _ h.2.1 (lt_of_lt_of_le h.2.2 hfix)⟩
  -- The heap below `heapStep`, outside the fixed block.
  have hK_foot : ∀ a, ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ a → a < ctx.heapStep →
      memFinal a = ctx.memMid a := fun a h1 h2 => hF_arr2 a (le_trans hsb h1) h2
  have hfoot_lo : ∀ a, heapFoot ctx.x a → ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ a := by
    rintro a ⟨iv, hiv, h1, -⟩
    exact le_trans (ctx.hState.2.2.1 iv hiv) h1
  have hgen : memFinal (ctx.b + dsGenOff) = ctx.memMid (ctx.b + dsGenOff) :=
    hK_hdr _ (by decide) (by decide)
  -- The edges of the new inDom of level `j` are below `eCap`.
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hInDomCap : ∀ e ∈ ctx.res.state.inDom ⟨ctx.j, by omega⟩, e < ctx.eCap := by
    intro e he
    have hnext := step_inv ctx.hVG₀ (le_trans hj_pos hj_le) ctx.hq ctx.hGm₀
      (canonicalSparsify_spec_absorb ctx.impl ctx.mMax) ctx.hBV ctx.hds ctx.hu_some ctx.hPref
    have hst1 : runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us
        (ctx.k + 1) = ctx.res.state := by
      simp [StepPosEpCtx.res, StepPosEpCtx.st, runState, ctx.hu_some]
    have hsub := hnext.1.inDom_sub ⟨ctx.j, by omega⟩
    rw [hst1] at hsub
    have hG'E : (ctx.G₀.applyBatch (ctx.us.take (ctx.k + 1))).E ⊆ ctx.st.G.E := by
      have hk := ctx.hPref ctx.k (le_refl _)
      have htake := take_succ_of_getElem? ctx.hu_some
      rw [htake, applyBatch_append, ← hk.G_eq]; exact E_applyUpdate_subset hdu.2
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (hG'E (hsub he))
  refine Exists.elim (rebuildStatePos (G₀ := ctx.G₀) (L := ctx.L) (q := ctx.q) (mMax := ctx.mMax)
      (vCap := ctx.vCap) (eCap := ctx.eCap) (b := ctx.b) (k := ctx.k) (impl := ctx.impl)
      (us := ctx.us) (u := ctx.u) (mem0 := ctx.mem0) (mem2 := ctx.mem2) (memFin := ctx.memMid)
      (memFinal := memFinal) (x := ctx.x) (r := r) (revJ := revJ) (sLists' := ctx.sLists')
      (heapStep := ctx.heapStep) (headHeap := ctx.headHeap) (r₁ := ctx.r₁)
      (retFinal := ctx.nextHeap + uhWords)
      ctx.hVG₀ ctx.hq ctx.hGm₀ ctx.hBV ctx.hds ctx.hu_some ctx.hPref ctx.hRev ctx.hj_pos
      ctx.hState ctx.hGV'_cap ⟨hr_L, hr_v, hr_e, hr_b, hr_j⟩ ctx.hfix_step
      ⟨le_trans (Nat.le_add_right _ _) hHS,
        le_trans hr1 (le_trans hU_n hnh)⟩
      ⟨(hK_hdr _ (by decide) (by decide)).trans hM_q, hF_t,
        (hK_hdr _ (by decide) (by decide)).trans hM_L,
        (hK_hdr _ (by decide) (by decide)).trans hM_vC,
        (hK_hdr _ (by decide) (by decide)).trans hM_eC,
        hgen ▸ hM_gen1, le_of_eq hgen.symm, hM_gen2, ctx.hgen_02⟩
      ⟨dynGraphAt_of_agree hM_G (hK_graph _ (Or.inl rfl)),
        dynGraphAt_of_agree hM_H (hK_graph _ (Or.inr rfl)), hF_aux⟩
      ⟨hM_Bk.of_agree_range fun a h1 h2 =>
          hF_arr a h1 (lt_trans h2 (domGen_lt_sBit ctx.b ctx.L ctx.vCap ctx.eCap)),
        fun e he => (hK_minH e he).symm ▸ hM_minH e he,
        fun i e => by
          by_cases he : e < ctx.eCap
          · rw [hK_minH e he]; exact hM_newB i e
          · have hnot : e ∉ ctx.res.state.H.E := fun h => he (hM_H.2.2.1 e h)
            constructor
            · intro h; exact absurd ((hM_newB i e).1 h).1 hnot
            · intro h; exact absurd h.1 hnot⟩
      (fun i hi =>
        have hiL : i.1 ≤ ctx.L := Nat.lt_succ_iff.mp i.2
        have h := hM_domLt i hi
        ⟨(hK_i i.1 hiL).1.trans h.1,
          fun e he => ⟨(hK_e i.1 hiL e he).1.trans (h.2.1 e he).1,
            (hK_e i.1 hiL e he).2.trans (h.2.1 e he).2⟩,
          fun v hv => ⟨(hK_v i.1 hiL v hv).1.trans (h.2.2 v hv).1,
            (hK_v i.1 hiL v hv).2.1.trans (h.2.2 v hv).2⟩⟩)
      (fun a ha => (hK_foot a (hfoot_lo a ha) (ctx.hfoot_lt a ha)).trans (hM_foot0 a ha))
      (by
        obtain ⟨hdPos, hdLe, hed, hpi, hrev⟩ := hM_lvlJ
        have hdom_j := (hK_i ctx.j hj_le).1
        refine ⟨hdom_j ▸ hdPos, by rw [hdom_j, hgen]; exact hdLe,
          fun e he => by
            simp only [(hK_e ctx.j hj_le e he).1, hdom_j, hgen]
            exact hed e he,
          fun e he => by
            rw [(hK_e ctx.j hj_le e (hInDomCap e he)).2]
            obtain ⟨hmw, hlo, hhi⟩ := hpi e he
            refine ⟨hmw.of_agree fun a h1 h2 => hF_heap a (le_trans hlo h1) ?_,
              le_trans (Nat.le_add_right _ _) hlo, le_trans hhi hnh⟩
            rw [mWalkEncode_length] at hhi
            omega,
          fun v hv => by
            obtain ⟨hrg, hnd, hmem, hll⟩ := hrev v hv
            simp only [(hK_v ctx.j hj_le v hv).1, hdom_j, hgen]
            refine ⟨hrg, hnd, hmem, ?_⟩
            split_ifs at hll ⊢
            · rw [(hK_v ctx.j hj_le v hv).2.1]
              exact (hll.of_agree fun a ha => hF_heap a ha.1 ha.2).mono
                fun a ha => ⟨le_trans (Nat.le_add_right _ _) ha.1, lt_of_lt_of_le ha.2 hnh⟩
            · exact hll⟩)
      (fun i hi =>
        have hiL : i.1 ≤ ctx.L := Nat.lt_succ_iff.mp i.2
        have h := hM_domGt i hi
        ⟨(hK_i i.1 hiL).1.trans h.1, fun e he => (hK_e i.1 hiL e he).1.trans (h.2.1 e he),
          fun v hv => (hK_v i.1 hiL v hv).1.trans (h.2.2 v hv)⟩)
      ctx.hSL2
      (fun i => by
        have hiL : i.1 ≤ ctx.L := Nat.lt_succ_iff.mp i.2
        have hSi := hM_S i
        by_cases hlt : i.1 < ctx.j
        · simp only [hlt, ↓reduceIte] at hSi
          exact ⟨(hK_i i.1 hiL).2.1.trans hSi.1, (hK_i i.1 hiL).2.2.trans hSi.2.1,
            fun v hv => (hK_v i.1 hiL v hv).2.2.trans (hSi.2.2.1 v hv)⟩
        · simp only [hlt, ↓reduceIte] at hSi
          have hs0 : ctx.mem2 (dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + i.1) = 0 :=
            (ctx.hSL2 i).2.1 (Nat.le_of_not_lt hlt)
          exact ⟨(hK_i i.1 hiL).2.1.trans (hSi.1.trans hs0.symm),
            (hK_i i.1 hiL).2.2.trans hSi.2.1,
            fun v hv => (hK_v i.1 hiL v hv).2.2.trans (hSi.2.2 v hv)⟩)
      (fun p hp => by
        rcases hp with hp | ⟨hp1, hp2⟩
        · exact (hK_foot p (hfoot_lo p hp) (ctx.hfoot_lt p hp)).trans
            ((hM_foot0 p hp).trans (ctx.hFoot_02 p hp).symm)
        · have hS0 := hM_S ⟨0, Nat.zero_lt_succ _⟩
          simp only [hj_pos, ↓reduceIte] at hS0
          exact (hF_heap p (le_trans hHS hp1)
            (lt_of_lt_of_le hp2 (le_trans hr1 hU_n))).trans
            (hS0.2.2.2 p hp1 hp2))
      ⟨fun v hv => ⟨hF_sb v hv, by rw [hK_vst v hv, hgen]; exact (hM_sbVst v hv).2⟩,
        fun e he => ⟨by rw [(hK_est e he).1, hgen]; exact (hM_eKept e he).1,
          by
            rw [(hK_est e he).2, hgen, (hM_eKept e he).2]
            exact le_trans (ctx.hKept_le e he) (le_trans ctx.hgen_02 hM_gen2)⟩⟩)
    fun x' hx' => ?_
  obtain ⟨hx'_v, hx'_e, hx'_iv, hState', hRev'⟩ := hx'
  refine ⟨ctx.nextHeap, uhWords, dPtr, restrictUpdate ctx.u ctx.st.H ++ c.recs, dL, x',
    hF_h0, hF_h1, hF_h2, hF_h3, hF_h4, hdP, hM_d_nh, rfl, hF_uh, hM_perm, hM_dNd, hM_dFin,
    listAt_of_agree (fun i hi => hF_heap _ (le_trans hdP (Nat.le_add_right _ _))
      (lt_of_lt_of_le (Nat.add_lt_add_left hi _) hM_d_nh)) hM_dAt,
    hF_zero, hx'_v, hx'_e, hx'_iv, hState', hRev', fun a ha hnm => ?_⟩
  have hside : a < ctx.b ∨ ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ a := by
    by_contra hnot
    push Not at hnot
    exact hnm (Or.inl ⟨hnot.1, by rw [ctx.hState.1, ctx.hState.2.1]; exact hnot.2⟩)
  rcases hside with h | h
  · exact (hF_low a h).trans (hM_frame0 a ha hnm)
  · exact (hK_foot a h ha).trans (hM_frame0 a ha hnm)

end

end MinCostFlow.DynSpanner.Program
