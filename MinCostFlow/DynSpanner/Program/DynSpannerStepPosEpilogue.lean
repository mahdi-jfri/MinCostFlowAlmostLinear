module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEpilogueDefs
import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueB
import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEpiloguePost
import MinCostFlow.DynSpanner.Program.DynSpannerStepAddr

/-!
# Common epilogue of a `0 < j` step: the proof

Proves `dsStepPosEpilogue_meetsContract`: from `StepPosMidPost`, the epilogue
`dsStepPosEpilogueStmt` (`DynSpannerStepPosEpilogueDefs.lean`) clears the `sBit` words of
`S_{j-1}`, empties the graph `J`, increments `t`, copies `U_H` to one contiguous batch, writes the
step header, and the memory then satisfies `StepOutPost`. The new state is rebuilt by
`rebuildStatePos` (`DynSpannerStepPosJoinB.lean`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

/-! ## Private helpers -/

private lemma restrictUpdate_length_eq {H : MGraph} {u : Update} {prefWords : ℕ}
    {mem : ℕ → ℕ} {a : ℕ} (hds : isDelOrSplit u)
    (hB : BatchBodyAt mem a H (restrictUpdate u H) prefWords) :
    (restrictUpdate u H).length = if 0 < prefWords then 1 else 0 := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e =>
    unfold restrictUpdate at hB ⊢
    by_cases he : e ∈ H.E
    · simp only [he, ↓reduceIte] at hB ⊢
      rcases hB with ⟨len, hle, ⟨rfl, _⟩, _⟩
      simp [show 0 < prefWords by omega]
    · simp only [he, ↓reduceIte] at hB ⊢
      have hw : prefWords = 0 := hB
      simp [hw]
  | split v v' St Sh =>
    simp only [restrictUpdate] at hB ⊢
    rcases hB with ⟨len, hle, hu, _⟩
    have hpos : 0 < len := by
      rcases hu with ⟨Lt, Lh, _, _, _, _, rfl, _⟩ | ⟨Lt, Lh, _, _, _, _, rfl, _⟩ <;> omega
    simp [show 0 < prefWords by omega]

private lemma delInsWords_le_four_mul {us : List Update} :
    delInsWords us ≤ 4 * us.length := by
  induction us with
  | nil => simp [delInsWords]
  | cons u us ih =>
    simp only [delInsWords, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    cases u <;> simp only [delInsWordLen] <;> omega

private lemma ep_runs_cost_mono {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {k₁ k₂ T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k₂ + c ≤ T) (hle : k₁ ≤ k₂) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k₁ + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', c, hr, hq, by omega⟩

private lemma ep_w16 {b L vCap eCap hs nh w : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ hs) (hhn : hs ≤ nh) (hnw : nh < 2 ^ w) : 16 < 2 ^ w := by
  have := dsFixedSize_pos L vCap eCap
  omega

/-- The side conditions of the frame of the epilogue, by region. -/
private lemma ep_frame_cases {a b t aux minH sb vc hs nh : ℕ} (hA1 : b + t < aux)
    (hA2 : aux ≤ minH) (hA3 : minH ≤ sb) (hA4 : sb + vc ≤ hs) (hA5 : hs ≤ nh) :
    (a < b → a < nh ∧ (a < hs ∨ hs + 5 ≤ a) ∧ a ≠ b + t ∧ (a < aux ∨ minH ≤ a) ∧
      (a < sb ∨ sb + vc ≤ a)) ∧
    (b ≤ a → a < aux → a ≠ b + t → a < nh ∧ (a < hs ∨ hs + 5 ≤ a) ∧ a ≠ b + t ∧
      (a < aux ∨ minH ≤ a) ∧ (a < sb ∨ sb + vc ≤ a)) ∧
    (minH ≤ a → a < sb → a < nh ∧ (a < hs ∨ hs + 5 ≤ a) ∧ a ≠ b + t ∧
      (a < aux ∨ minH ≤ a) ∧ (a < sb ∨ sb + vc ≤ a)) ∧
    (sb + vc ≤ a → a < hs → a < nh ∧ (a < hs ∨ hs + 5 ≤ a) ∧ a ≠ b + t ∧
      (a < aux ∨ minH ≤ a) ∧ (a < sb ∨ sb + vc ≤ a)) ∧
    (hs + 5 ≤ a → a < nh → a < nh ∧ (a < hs ∨ hs + 5 ≤ a) ∧ a ≠ b + t ∧
      (a < aux ∨ minH ≤ a) ∧ (a < sb ∨ sb + vc ≤ a)) ∧
    (aux ≤ a → a < minH → a < hs ∧ a < nh ∧ a ≠ b + t) ∧
    (a < vc → sb + a < hs ∧ sb + a < nh ∧ sb + a ≠ b + t ∧ minH ≤ sb + a) := by
  omega

/-- A vertex outside the list `sPrevList` of `S_{j-1}` has `sBit = 0` before the epilogue. -/
private lemma ep_sBit_zero (ctx : StepPosEpCtx) {v m : ℕ} (hvS : v ∉ ctx.sPrevList)
    (h : m = if v ∈ ctx.st.S_level ⟨chooseLevel ctx.L ctx.q (ctx.k + 1) - 1,
        by have := chooseLevel_le ctx.L ctx.q (ctx.k + 1); omega⟩ ∪
        touchedVertices ctx.st.G ctx.u then 1 else 0) : m = 0 := by
  have hj_pos : 0 < ctx.j := ctx.hj_pos
  have hnotS : v ∉ ctx.st.S_level ⟨chooseLevel ctx.L ctx.q (ctx.k + 1) - 1,
      by have := chooseLevel_le ctx.L ctx.q (ctx.k + 1); omega⟩ ∪
      touchedVertices ctx.st.G ctx.u := by
    intro hmem
    have hj_le : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
    have hSL := ctx.hSL2 ⟨ctx.j - 1, by omega⟩
    have hlt' : ctx.j - 1 < ctx.j := by omega
    simp only [hlt', ↓reduceIte] at hSL
    exact hvS (ctx.hsPrev_eq ▸ (hSL.2.2.2.2.2.1 v).mpr hmem)
  simp only [h, hnotS, ↓reduceIte]

private lemma ep_setup_regs {w L vCap eCap b : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem regs : ℕ → ℕ} {pos k T : ℕ}
    {rest : Stmt} {Post : Outcome → State → Prop}
    (h16 : 16 < 2 ^ w) (hfix : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hr0 : regs 0 = b)
    (hL : mem (b + dsLOff) = L) (hV : mem (b + dsVCapOff) = vCap) (hE : mem (b + dsECapOff) = eCap)
    (hcont : ∀ regs' : ℕ → ℕ,
      (∀ r ≤ 6, regs' r = regs r) →
      (regs' 11 = dsAuxPtr b vCap eCap ∧ regs' 16 = dsSBitBase b L vCap eCap) →
      ∃ o st' c, Runs w p ω rest { regs := regs', mem := mem, pos := pos } o st' c ∧
        Post o st' ∧ k + 115 + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 7 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 8 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 9 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 10 (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 8)) (.bin .mul (.const 9) (.reg 9)))) ;;
       .assign 11 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize))
         (.bin .mul (.const 2) (.reg 10))) ;;
       .assign 12 (.bin .add (.reg 11) (.reg 10)) ;;
       .assign 13 (.bin .add (.reg 7) (.const 1)) ;;
       .assign 14 (.bin .add (.bin .add (.reg 12) (.bin .mul (.const 3) (.reg 9)))
         (.bin .mul (.const 2) (.reg 13))) ;;
       .assign 15 (.bin .add (.reg 14)
         (.bin .add (.reg 13)
           (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 13) (.reg 9)))
             (.bin .mul (.const 2) (.bin .mul (.reg 13) (.reg 8)))))) ;;
       .assign 16 (.bin .add (.reg 15)
         (.bin .add (.bin .mul (.const 2) (.reg 13)) (.bin .mul (.reg 13) (.reg 8)))) ;;
       rest)
      { regs := regs, mem := mem, pos := pos } o st' c ∧ Post o st' ∧ k + c ≤ T := by
  have hc : ∀ n ≤ 16, n < 2 ^ w := fun _ hn => lt_of_le_of_lt hn h16
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    fixed_layout_order b L vCap eCap
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have haux : dsAuxPtr b vCap eCap = (b + dsHdrSize) + 2 * dynGraphSize vCap eCap := by
    simp only [dsAuxPtr, dsHPtr, dsGPtr]; ring
  have hdom : dsDomGenBase b L vCap eCap = (dsMinHBase b vCap eCap + 3 * eCap) + 2 * (L + 1) := by
    simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]; ring
  have hsG : dsSGenBase b L vCap eCap = dsDomGenBase b L vCap eCap +
      ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) := by
    simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; ring
  have hsB : dsSBitBase b L vCap eCap = dsSGenBase b L vCap eCap +
      (2 * (L + 1) + (L + 1) * vCap) := by
    simp only [dsSBitBase, dsSHeadBase, dsVSGenBase]; ring
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (hc dsLOff (by decide))) (by simp only [dsLOff, dsHdrSize] at f0 ⊢; omega)) hL) ?_
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (hc dsVCapOff (by decide))) (by simp only [dsVCapOff, dsHdrSize] at f0 ⊢; omega)) hV) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (hc dsECapOff (by decide))) (by simp only [dsECapOff, dsHdrSize] at f0 ⊢; omega)) hE) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (by
      have h1 : dynGraphSize vCap eCap = 4 + (7 * vCap + 9 * eCap) := by omega
      rw [h1]
      exact Expr.eval_add (Expr.eval_const (hc 4 (by decide)))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (hc 7 (by decide))) (Expr.eval_reg_of_eq (by simp)) (by omega))
          (Expr.eval_mul (Expr.eval_const (hc 9 (by decide))) (Expr.eval_reg_of_eq (by simp)) (by omega))
          (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := dsAuxPtr b vCap eCap)
    (by
      rw [haux]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
          (Expr.eval_const (hc dsHdrSize (by decide))) (by omega))
        (Expr.eval_mul (Expr.eval_const (hc 2 (by decide))) (Expr.eval_reg_of_eq (by simp)) (by omega))
        (by omega)) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
  refine runs_seq_assign_le (v := L + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (hc 1 (by decide))) (by omega)) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (by
      rw [hdom]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_mul (Expr.eval_const (hc 3 (by decide))) (Expr.eval_reg_of_eq (by simp)) (by omega))
          (by omega))
        (Expr.eval_mul (Expr.eval_const (hc 2 (by decide))) (Expr.eval_reg_of_eq (by simp)) (by omega))
        (by omega)) ?_
  refine runs_seq_assign_le (v := dsSGenBase b L vCap eCap)
    (by
      rw [hsG]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (hc 2 (by decide)))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              (by omega))
            (Expr.eval_mul (Expr.eval_const (hc 2 (by decide)))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega))
              (by omega)) (by omega)) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := dsSBitBase b L vCap eCap)
    (by
      rw [hsB]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (hc 2 (by decide))) (Expr.eval_reg_of_eq (by simp)) (by omega))
          (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega))
          (by omega)) (by omega)) ?_
  refine ep_runs_cost_mono (hcont _ (fun r hr => by
      simp only [Function.update_of_ne (show r ≠ 16 by omega),
        Function.update_of_ne (show r ≠ 15 by omega), Function.update_of_ne (show r ≠ 14 by omega),
        Function.update_of_ne (show r ≠ 13 by omega), Function.update_of_ne (show r ≠ 12 by omega),
        Function.update_of_ne (show r ≠ 11 by omega), Function.update_of_ne (show r ≠ 10 by omega),
        Function.update_of_ne (show r ≠ 9 by omega), Function.update_of_ne (show r ≠ 8 by omega),
        Function.update_of_ne (show r ≠ 7 by omega)])
    ⟨by simp, by simp⟩) ?_
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
  omega

/-! ## Main contract theorem -/

public section

set_option maxHeartbeats 1000000 in
/-- `dsStepPosEpilogueStmt` meets `dsStepPosEpilogueContract`. -/
theorem dsStepPosEpilogue_meetsContract (ctx : StepPosEpCtx) {p : Program}
    {bAux bPhase bEdge bOps bEp : ℕ}
    (hpAux : p.HasAt bAux stepAuxProcs)
    (hpPhase : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpEp : p.HasAt bEp (stepPosEpilogueProcs bAux bPhase)) :
    MeetsContract ctx.w p (bEp + stepPosEpilogueIdx) (dsStepPosEpilogueContract ctx) := by
  refine meetsContract_of_runs
    (hpEp.get (i := stepPosEpilogueIdx) (by simp [stepPosEpilogueProcs, stepPosEpilogueIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, rfl⟩
  simp only [stepPosEpilogueProcs, stepPosEpilogueIdx, List.getElem_cons_zero]
  dsimp only [dsStepPosEpilogueStmt]
  -- Unpack `StepPosMidPost`
  obtain ⟨uhTailHdr, dPtr, c, r, revJ, dL, hB⟩ := ctx.hMidPost
  have hB' := hB
  obtain ⟨hM_hdr0, hM_hdr1, hM_hdr2, hM_aff_uh, hM_uh_d, hM_d_nh, hM_zero,
    hM_cnt, hM_body, hM_perm, hM_delIns, hM_dNd, hM_dFin, hM_dAt,
    hr_L, hr_v, hr_e, hr_b, hr_j,
    hM_q, hM_t, hM_L, hM_vC, hM_eC, hM_gen1, hM_gen2, hM_gen3,
    hM_G, hM_H, hM_Aux, hM_Bk, hM_minH, hM_newB,
    hM_domLt, hM_foot0, hM_lvlJ, hM_domGt, hM_S, hM_sbVst, hM_eKept,
    hM_prefAg, hM_sPrevAt, hM_frame0⟩ := hB'
  have hj_le : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hj_pos : 0 < ctx.j := ctx.hj_pos
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hpref_len : (restrictUpdate ctx.u ctx.st.H).length = if 0 < ctx.prefWords then 1 else 0 :=
    restrictUpdate_length_eq hdu.2 ctx.hPrefBody
  have hc_words_eq : c.words = delInsWords c.recs :=
    (hM_body ctx.st.H).delIns_words hM_delIns
  have hc_recs_le_UH : c.recs.length ≤ ctx.res.UH.length := by
    have h1 : (restrictUpdate ctx.u ctx.st.H ++ c.recs).length = ctx.res.UH.length :=
      hM_perm.length_eq
    rw [List.length_append] at h1; omega
  have hc_words_le : c.words ≤ 4 * ctx.res.UH.length := by
    rw [hc_words_eq]; exact le_trans delInsWords_le_four_mul (Nat.mul_le_mul_left 4 hc_recs_le_UH)
  have hc_words_le_size : c.words ≤ c.size := by
    have h1 := List.length_filter_le (fun e => decide (e ∉ c.da.X))
      (bucketsCat c.da.B c.da.lo (c.da.hi - c.da.lo))
    have h2 := List.length_filter_le (fun e => decide (e ∉ c.Y)) c.es
    simp only [UTCtx.words, UTCtx.size, delList, insList]
    omega
  -- Word-size and layout bounds (all pure `ℕ` from `ctx.hEnd_ltw` and `fixed_layout_order`)
  have hHN : ctx.heapStep ≤ ctx.nextHeap := by
    have h1 : ∀ hs pw hh r1 ha sp uh cs dp dl nh : ℕ, hs + 5 + pw ≤ hh → hh ≤ r1 → r1 ≤ ha →
        ha + 2 + sp ≤ uh → uh + 1 + cs ≤ dp → dp + dl ≤ nh → hs ≤ nh := by intros; omega
    exact h1 _ _ _ _ _ _ _ _ _ _ _ ctx.hhead_in.1 ctx.hhead_in.2.1 ctx.hhead_in.2.2 hM_aff_uh
      hM_uh_d hM_d_nh
  have h16_lt : 16 < 2 ^ ctx.w :=
    ep_w16 ctx.hfix_step hHN
      (lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt (Nat.le_add_right _ _) ctx.hEnd_ltw))
  have hc_lt : ∀ n ≤ 16, n < 2 ^ ctx.w := fun _ hn => lt_of_le_of_lt hn h16_lt
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hQo : dsQOff = 0 := rfl
  have hTo : dsTOff = 1 := rfl
  have hLo : dsLOff = 2 := rfl
  have hVo : dsVCapOff = 3 := rfl
  have hEo : dsECapOff = 4 := rfl
  have hGo : dsGenOff = 5 := rfl
  have hHo : dsHdrSize = 6 := rfl
  have hdgs : dynGraphSize ctx.vCap ctx.eCap = 4 + 7 * ctx.vCap + 9 * ctx.eCap := rfl
  have hfix_step := ctx.hfix_step
  have hhead_in := ctx.hhead_in
  have hEnd_ltw : ctx.nextHeap + ctx.prefWords + 4 * ctx.res.UH.length < 2 ^ ctx.w :=
    ctx.hEnd_ltw
  have hsPrev_cap : ∀ v ∈ ctx.sPrevList, v < ctx.vCap := by
    intro v hv
    rw [ctx.hsPrev_eq] at hv
    have hSL := ctx.hSL2 ⟨ctx.j - 1, by omega⟩
    have hlt' : ctx.j - 1 < ctx.j := by omega
    simp only [hlt', ↓reduceIte] at hSL
    exact hSL.2.2.1 v ((hSL.2.2.2.2.2.1 v).mp hv)
  have hsPrev_len_le : ctx.sPrevList.length ≤ ctx.vCap := by
    rw [ctx.hsPrev_eq]
    have hSL := ctx.hSL2 ⟨ctx.j - 1, by omega⟩
    exact list_length_le_of_nodup_lt hSL.2.2.2.2.1 (fun v hv => by
      have hlt' : ctx.j - 1 < ctx.j := by omega
      simp only [hlt', ↓reduceIte] at hSL
      exact hSL.2.2.1 v ((hSL.2.2.2.2.2.1 v).mp hv))
  have hsPrev_le_uh : ctx.heapAff + 2 + ctx.sPrevList.length < 2 ^ ctx.w := by omega
  -- Run prefix setup
  refine runs_start_le ?_
  refine ep_setup_regs h16_lt (by omega) (by simp) hM_L hM_vC hM_eC ?_
  intro regs1 hR1_old hR1_new
  obtain ⟨h1_11, h1_16⟩ := hR1_new
  have h1_0 : regs1 0 = ctx.b := (hR1_old 0 (by decide)).trans (by simp)
  have h1_2 : regs1 2 = ctx.prefWords := (hR1_old 2 (by decide)).trans (by simp)
  have h1_3 : regs1 3 = ctx.heapStep := (hR1_old 3 (by decide)).trans (by simp)
  have h1_4 : regs1 4 = ctx.heapAff := (hR1_old 4 (by decide)).trans (by simp)
  have h1_5 : regs1 5 = ctx.sPrevList.length := (hR1_old 5 (by decide)).trans (by simp)
  have h1_6 : regs1 6 = ctx.nextHeap := (hR1_old 6 (by decide)).trans (by simp)
  -- Call 1: `dsClearSBit [sBit, heapAff + 2, sPrevLen]`
  refine runs_seq_call_le (vs := [dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.heapAff + 2, ctx.sPrevList.length])
    (dsClearSBit_meetsContract (w := ctx.w) (vCap := ctx.vCap) (vs := ctx.sPrevList) hpAux)
    (evalArgs_cons (Expr.eval_reg_of_eq h1_16) <|
      evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq h1_4)
        (Expr.eval_const (hc_lt 2 (by decide))) (by omega)) <|
      evalArgs_cons (Expr.eval_reg_of_eq h1_5) <|
      evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.heapAff + 2, rfl, ctx.hw16, by omega, by omega,
      Or.inl (by omega), hM_sPrevAt, hsPrev_cap⟩ ?_
  rintro _ mem1 pos1 ⟨_, _, hargs1, _, hSB1_clr, hSB1_fr⟩
  simp only [List.cons.injEq, and_true] at hargs1
  obtain ⟨rfl, rfl⟩ := hargs1
  have h1_ag : ∀ addr, (addr < dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap ∨
      dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.vCap ≤ addr) →
      mem1 addr = ctx.memMid addr := fun addr ha =>
    hSB1_fr addr fun v hv => by have := hsPrev_cap v hv; omega
  -- Call 2: `clearAuxGraph [auxPtr]`
  refine runs_seq_call_le (vs := [dsAuxPtr ctx.b ctx.vCap ctx.eCap])
    (clearAuxGraph_meetsContract (w := ctx.w) (vCap := ctx.vCap) (eCap := ctx.eCap) (A := ctx.J)
      hpPhase hpEdge hpOps)
    (evalArgs_cons (Expr.eval_reg_of_eq (by simp [h1_11])) (evalArgs_nil _ _))
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv; omega)
    ⟨dsAuxPtr ctx.b ctx.vCap ctx.eCap, rfl, ctx.hw16, by omega,
      dynGraphAt_of_agree hM_Aux fun a h1 h2 => h1_ag a (Or.inl (by omega))⟩ ?_
  rintro _ mem2a pos2 ⟨_, hargs2, _, hAux2_empty, hAux2_fr⟩
  dsimp only at hAux2_fr
  simp only [List.cons.injEq, and_true] at hargs2
  subst hargs2
  -- Step 3: `t := mem[b + dsTOff] + 1; mem[b + dsTOff] := t`
  have ht_mem2a : mem2a (ctx.b + dsTOff) = ctx.st.t := by
    rw [hAux2_fr _ (Or.inl (by simp only [dsTOff, dsHdrSize] at f0 ⊢; omega)),
      h1_ag _ (Or.inl (by simp only [dsTOff, dsHdrSize] at f0 ⊢; omega))]
    exact hM_t
  have ht_eq_k : ctx.st.t = ctx.k := (ctx.hPref ctx.k (le_refl _)).t_eq
  have ht1_lt : ctx.st.t + 1 < 2 ^ ctx.w := by rw [ht_eq_k]; exact ctx.ht_ltw
  refine runs_seq_assign_le (v := ctx.st.t + 1)
    (Expr.eval_add
      (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_0]))
          (Expr.eval_const (hc_lt dsTOff (by decide)))
          (by simp only [dsTOff, dsHdrSize] at f0 ⊢; omega)) ht_mem2a)
      (Expr.eval_const (hc_lt 1 (by decide))) ht1_lt) ?_
  let mem3 := Function.update mem2a (ctx.b + dsTOff) (ctx.st.t + 1)
  refine runs_seq_store_le (x := ctx.b + dsTOff) (v := ctx.st.t + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_0]))
      (Expr.eval_const (hc_lt dsTOff (by decide)))
      (by simp only [dsTOff, dsHdrSize] at f0 ⊢; omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  have h3_ag_ge_hs : ∀ addr, ctx.heapStep ≤ addr → mem3 addr = ctx.memMid addr := fun addr ha => by
    have hne : addr ≠ ctx.b + dsTOff := by simp only [dsTOff, dsHdrSize] at f0 ⊢; omega
    simp only [mem3, Function.update_of_ne hne]
    rw [hAux2_fr addr (Or.inr (by omega)), h1_ag addr (Or.inr (by omega))]
  -- Step 4: load `uhTailHdr`, `dPtr`, `dLen`, `tailCount`, compute `prefCount`
  refine runs_seq_assign_le (v := uhTailHdr)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [h1_3]))
      ((h3_ag_ge_hs _ (le_refl _)).trans hM_hdr0)) ?_
  refine runs_seq_assign_le (v := dPtr)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_3]))
      (Expr.eval_const (hc_lt 1 (by decide))) (by omega))
      ((h3_ag_ge_hs _ (by omega)).trans hM_hdr1)) ?_
  refine runs_seq_assign_le (v := dL.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_3]))
      (Expr.eval_const (hc_lt 2 (by decide))) (by omega))
      ((h3_ag_ge_hs _ (by omega)).trans hM_hdr2)) ?_
  refine runs_seq_assign_le (v := c.recs.length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp))
      ((h3_ag_ge_hs _ (by omega)).trans hM_cnt)) ?_
  let prefCount := if 0 < ctx.prefWords then 1 else 0
  refine runs_seq_assign_le (v := prefCount)
    (Expr.eval_lt_op (Expr.eval_const (hc_lt 0 (by decide)))
      (Expr.eval_reg_of_eq (by simp [h1_2])) (hc_lt 1 (by decide))) ?_
  -- Call 3: `dsCopyWords [heapStep + 5, nextHeap, prefWords]`
  refine runs_seq_call_le (vs := [ctx.heapStep + 5, ctx.nextHeap, ctx.prefWords])
    (dsCopyWords_meetsContract (w := ctx.w) (n := ctx.prefWords) hpAux)
    (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_3]))
        (Expr.eval_const (hc_lt 5 (by decide))) (by omega)) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [h1_6])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [h1_2])) <|
      evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨ctx.heapStep + 5, ctx.nextHeap, rfl, ctx.hw16, by omega, by omega, Or.inl (by omega)⟩ ?_
  rintro _ mem4 pos4 ⟨_, _, hargs4, _, hCW4_cp, hCW4_fr⟩
  dsimp only at hCW4_cp hCW4_fr
  simp only [List.cons.injEq, and_true] at hargs4
  obtain ⟨rfl, rfl⟩ := hargs4
  -- Call 4: `tailWords := dsCopyDelIns [uhTailHdr + 1, nextHeap + prefWords, c.recs.length]`
  have hBody4 : BatchBodyAt mem4 (uhTailHdr + 1)
      (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)) c.recs c.words :=
    (hM_body _).of_agree fun i hi =>
      (hCW4_fr _ (Or.inl (by omega))).trans (h3_ag_ge_hs _ (by omega))
  refine runs_seq_call_le (vs := [uhTailHdr + 1, ctx.nextHeap + ctx.prefWords, c.recs.length])
    (dsCopyDelIns_meetsContract (w := ctx.w)
      (G := ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
      (us := c.recs) (tot := c.words) hpAux)
    (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_const (hc_lt 1 (by decide))) (by omega)) <|
      evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_6]))
        (Expr.eval_reg_of_eq (by simp [h1_2])) (by omega)) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp)) <|
      evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨uhTailHdr + 1, ctx.nextHeap + ctx.prefWords, rfl, ctx.hw16, by omega, by omega,
      Or.inl (by omega), hBody4, hM_delIns⟩ ?_
  rintro tailWords mem5 pos5 ⟨_, _, hargs5, htw_eq, hCD5_cp, hCD5_fr⟩
  dsimp only at hCD5_cp hCD5_fr
  simp only [List.cons.injEq, and_true] at hargs5
  obtain ⟨rfl, rfl⟩ := hargs5
  subst htw_eq
  -- Step 6: compute `uhCount`, `uhWords`, store 5-word header, return `nextHeap + uhWords`
  let uhCount := prefCount + c.recs.length
  let uhWords := ctx.prefWords + c.words
  have huhCount_lt : uhCount < 2 ^ ctx.w := by
    have : uhCount = ctx.res.UH.length := by
      have := hM_perm.length_eq
      rw [List.length_append, hpref_len] at this
      exact this
    omega
  have huhWords_lt : uhWords < 2 ^ ctx.w := by dsimp only [uhWords]; omega
  have hRet_lt : ctx.nextHeap + uhWords < 2 ^ ctx.w := by dsimp only [uhWords]; omega
  have hRet_le : ctx.nextHeap + uhWords ≤ ctx.nextHeap + ctx.prefWords + 4 * ctx.res.UH.length := by
    dsimp only [uhWords]; omega
  refine runs_seq_assign_le (v := uhCount)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) huhCount_lt) ?_
  refine runs_seq_assign_le (v := uhWords)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_2])) (Expr.eval_reg_of_eq (by simp)) huhWords_lt) ?_
  let memF0 := Function.update mem5 ctx.heapStep ctx.nextHeap
  let memF1 := Function.update memF0 (ctx.heapStep + 1) uhCount
  let memF2 := Function.update memF1 (ctx.heapStep + 2) uhWords
  let memF3 := Function.update memF2 (ctx.heapStep + 3) dPtr
  let memFinal := Function.update memF3 (ctx.heapStep + 4) dL.length
  refine runs_seq_store_le (x := ctx.heapStep) (v := ctx.nextHeap)
    (Expr.eval_reg_of_eq (by simp [h1_3])) (Expr.eval_reg_of_eq (by simp [h1_6])) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 1) (v := uhCount)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_3]))
      (Expr.eval_const (hc_lt 1 (by decide))) (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 2) (v := uhWords)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_3]))
      (Expr.eval_const (hc_lt 2 (by decide))) (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 3) (v := dPtr)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_3]))
      (Expr.eval_const (hc_lt 3 (by decide))) (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 4) (v := dL.length)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_3]))
      (Expr.eval_const (hc_lt 4 (by decide))) (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
  -- Build `StepOutPost` on `memFinal`
  have hF_5 : ∀ a, (a < ctx.heapStep ∨ ctx.heapStep + 5 ≤ a) → memFinal a = mem5 a := fun a ha => by
    simp only [memFinal, memF3, memF2, memF1, memF0,
      Function.update_of_ne (show a ≠ ctx.heapStep + 4 by omega),
      Function.update_of_ne (show a ≠ ctx.heapStep + 3 by omega),
      Function.update_of_ne (show a ≠ ctx.heapStep + 2 by omega),
      Function.update_of_ne (show a ≠ ctx.heapStep + 1 by omega),
      Function.update_of_ne (show a ≠ ctx.heapStep by omega)]
  have h5_3 : ∀ a, a < ctx.nextHeap → mem5 a = mem3 a := fun a ha =>
    (hCD5_fr a (Or.inl (by omega))).trans (hCW4_fr a (Or.inl ha))
  have hF_mid : ∀ a, a < ctx.nextHeap → (a < ctx.heapStep ∨ ctx.heapStep + 5 ≤ a) →
      a ≠ ctx.b + dsTOff →
      (a < dsAuxPtr ctx.b ctx.vCap ctx.eCap ∨ dsMinHBase ctx.b ctx.vCap ctx.eCap ≤ a) →
      (a < dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap ∨
        dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.vCap ≤ a) →
      memFinal a = ctx.memMid a := fun a h1 h2 h3 h4 h5 => by
    rw [hF_5 a h2, h5_3 a h1]
    simp only [mem3, Function.update_of_ne h3]
    rw [hAux2_fr a (by rcases h4 with h | h; exacts [Or.inl h, Or.inr (by omega)]), h1_ag a h5]
  have hF_gen : memFinal (ctx.b + dsGenOff) = ctx.memMid (ctx.b + dsGenOff) :=
    hF_mid _ (by omega) (Or.inl (by omega)) (by simp [dsGenOff, dsTOff])
      (Or.inl (by omega)) (Or.inl (by omega))
  have hF_t : memFinal (ctx.b + dsTOff) = ctx.st.t + 1 := by
    rw [hF_5 _ (Or.inl (by simp only [dsTOff, dsHdrSize] at f0 ⊢; omega)),
      h5_3 _ (by simp only [dsTOff, dsHdrSize] at f0 ⊢; omega)]
    exact Function.update_self _ _ _
  -- The words of the new memory, region by region.
  have hbo := block_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hFC := fun a => ep_frame_cases (a := a) hbo.1
    (le_trans (Nat.le_add_right _ _) (le_of_eq hbo.2.1)) hbo.2.2.1
    (le_trans hbo.2.2.2 hfix_step) hHN
  have hF_sb : ∀ v < ctx.vCap, memFinal (dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap + v) = 0 := by
    intro v hv
    have h := (hFC v).2.2.2.2.2.2 hv
    rw [hF_5 _ (Or.inl h.1), h5_3 _ h.2.1]
    simp only [mem3, Function.update_of_ne h.2.2.1]
    rw [hAux2_fr _ (Or.inr (le_trans (le_of_eq hbo.2.1) h.2.2.2))]
    by_cases hvS : v ∈ ctx.sPrevList
    · exact hSB1_clr v hvS
    · have hne : ∀ w ∈ ctx.sPrevList, dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap + v ≠
          dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap + w := fun w hw heq =>
        hvS ((Nat.add_left_cancel heq) ▸ hw)
      rw [hSB1_fr _ hne]
      exact ep_sBit_zero ctx hvS (hM_sbVst v hv).1
  have hF_aux : DynGraphAt memFinal (dsAuxPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap ctx.eCap
      emptyMGraph :=
    dynGraphAt_of_agree hAux2_empty fun a h1 h2 => by
      have h := (hFC a).2.2.2.2.2.1 h1 (hbo.2.1 ▸ h2)
      rw [hF_5 a (Or.inl h.1), h5_3 a h.2.1]
      simp only [mem3, Function.update_of_ne h.2.2]
  have hPref_F : BatchBodyAt memFinal ctx.nextHeap ctx.st.H (restrictUpdate ctx.u ctx.st.H)
      ctx.prefWords :=
    ctx.hPrefBody.copy fun i hi => by
      rw [hF_5 _ (Or.inr (by omega)), hCD5_fr _ (Or.inl (by omega)), hCW4_cp i hi]
      exact (h3_ag_ge_hs _ (by omega)).trans (hM_prefAg _ (by omega) (by omega))
  have hTail_F : BatchBodyAt memFinal (ctx.nextHeap + ctx.prefWords)
      (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)) c.recs c.words :=
    hBody4.copy fun i hi => by
      rw [hF_5 _ (Or.inr (by omega))]
      exact hCD5_cp i hi
  have hUH_len : (restrictUpdate ctx.u ctx.st.H ++ c.recs).length = uhCount := by
    rw [List.length_append, hpref_len]
  have hPost := stepPosEp_post ctx hB (memFinal := memFinal) (uhWords := uhWords)
    (fun a ha => have h := (hFC a).1 ha; hF_mid a h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun a h1 h2 h3 => have h := (hFC a).2.1 h1 h2 h3; hF_mid a h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun a h1 h2 => have h := (hFC a).2.2.1 h1 h2; hF_mid a h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun a h1 h2 => have h := (hFC a).2.2.2.1 h1 h2
      hF_mid a h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun a h1 h2 => have h := (hFC a).2.2.2.2.1 h1 h2
      hF_mid a h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    hF_t hF_aux hF_sb
    (by simp [memFinal, memF3, memF2, memF1, memF0])
    (by rw [hUH_len]; simp [memFinal, memF3, memF2, memF1])
    (by simp [memFinal, memF3, memF2])
    (by simp [memFinal, memF3])
    (by simp [memFinal])
    (hPref_F.append hTail_F)
    (fun a ha => by
      rw [hF_5 a (Or.inr (by omega)), hCD5_fr a (Or.inr (by omega)), hCW4_fr a (Or.inr (by omega))]
      exact (h3_ag_ge_hs a (by omega)).trans (hM_zero a (by omega)))
  have hGenF : memFinal (ctx.b + dsGenOff) ≤ ctx.mem2 (ctx.b + dsGenOff) + 3 + ctx.J.m := by
    rw [hF_gen]; exact hM_gen3
  have hUHW : memFinal (ctx.heapStep + 2) ≤ ctx.prefWords + 4 * ctx.res.UH.length := by
    have h2 : memFinal (ctx.heapStep + 2) = uhWords := by simp [memFinal, memF3, memF2]
    rw [h2]; omega
  refine runs_ret_le (v := ctx.nextHeap + uhWords)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_6])) (Expr.eval_reg_of_eq (by simp))
      hRet_lt)
    ⟨hPost, hRet_le, hGenF, hUHW,
      fun a h1 h2 => have h := (hFC a).2.2.2.2.1 h1 h2; hF_mid a h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2,
      Nat.le_add_right _ _⟩ ?_
  simp only [dsStepPosEpilogueContract, dsStepPosEpilogueCost, dsClearSBitContract,
    clearAuxGraphContract, dsCopyWordsContract, dsCopyDelInsContract,
    Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
  omega

end

end MinCostFlow.DynSpanner.Program
