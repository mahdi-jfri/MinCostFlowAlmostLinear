module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEmptyPost
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNERegs

/-!
# The empty `E_aff` branch of a `0 < j` step: the contract theorem

Proves `dsStepPosEmpty_meetsContract`. When `E_aff = ∅`, the procedure `dsStepPosEmptyStmt`
(`DynSpannerStepPosEmptyDefs.lean`) computes the addresses of the state block from its header,
calls `dsStepFinishStmt` with no new edge for level `j` (the records of `U_H`, the new buckets,
the cleared levels above `j`, and the empty walk table of level `j`), stores the three words
`[uhTailHdr, dPtr, 0]` at `heapStep`, and returns `dPtr`. The memory afterwards satisfies
`StepPosMidPost` by `stepPosE_midPost` (`DynSpannerStepPosEmptyPost.lean`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

private lemma runs_cost_start_e {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {T : ℕ} {Post : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Post o st' ∧ 0 + c ≤ T) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Post o st' ∧ c ≤ T := by
  simpa using h

private lemma runs_cost_mono_e {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {k₁ k₂ T : ℕ} {Post : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Post o st' ∧ k₂ + c ≤ T) (hle : k₁ ≤ k₂) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Post o st' ∧ k₁ + c ≤ T := by
  rcases h with ⟨o, st', c, hR, hP, hC⟩
  exact ⟨o, st', c, hR, hP, by omega⟩

private lemma stepPosE_fixed_lt (b L vCap eCap tw : ℕ) (h : b + dsFixedSize L vCap eCap < tw) :
    dsGPtr b < tw ∧ dsHPtr b vCap eCap < tw ∧ dsAuxPtr b vCap eCap < tw ∧
    dsMinHBase b vCap eCap < tw ∧ dsHNextBase b vCap eCap < tw ∧
    dsHHeadBase b vCap eCap < tw ∧ dsHDegDummyBase b L vCap eCap < tw ∧
    dsDomGenBase b L vCap eCap < tw ∧ dsSGenBase b L vCap eCap < tw ∧
    dgEPresBase (dsHPtr b vCap eCap) vCap < tw ∧
    dsHPtr b vCap eCap + 4 < tw ∧ 7 * vCap < tw := by
  obtain ⟨hn, hh, hd, hm, hg, hH, ha, hdg, hsg, -, -, -, -⟩ :=
    stepPosNE_fixed_bases_lt_w b L vCap eCap tw h
  have h5 : dgEPresBase (dsHPtr b vCap eCap) vCap + 9 * eCap = dsAuxPtr b vCap eCap := by
    simp only [dgEPresBase, dsAuxPtr, dynGraphSize]; omega
  have h7 : dsHPtr b vCap eCap + 4 + 7 * vCap = dgEPresBase (dsHPtr b vCap eCap) vCap := rfl
  exact ⟨hg, hH, ha, hm, hn, hh, hd, hdg, hsg, by omega, by omega, by omega⟩

/-- The bounds that the first sixteen assignments of `dsStepPosEmptyStmt` need. Each follows
from the next address of the layout being below the end of the state block. -/
private lemma stepPosE_setup_bounds (b L vCap eCap tw : ℕ)
    (h : b + dsFixedSize L vCap eCap < tw) :
    (b + dsLOff < tw ∧ b + dsVCapOff < tw ∧ b + dsECapOff < tw ∧
      7 * vCap < tw ∧ 9 * eCap < tw ∧ 7 * vCap + 9 * eCap < tw ∧
      4 + (7 * vCap + 9 * eCap) < tw ∧
      b + dsHdrSize < tw ∧ dsGPtr b + dynGraphSize vCap eCap < tw ∧
      dsHPtr b vCap eCap + dynGraphSize vCap eCap < tw ∧
      dsAuxPtr b vCap eCap + dynGraphSize vCap eCap < tw ∧
      dsMinHBase b vCap eCap + eCap < tw) ∧
    (2 * eCap < tw ∧ dsHNextBase b vCap eCap + 2 * eCap < tw ∧ L + 1 < tw ∧
      dsHHeadBase b vCap eCap + (L + 1) < tw ∧
      dsHDegDummyBase b L vCap eCap + (L + 1) < tw) ∧
    ((L + 1) * eCap < tw ∧ (L + 1) * vCap < tw ∧
      2 * ((L + 1) * eCap) < tw ∧ 2 * ((L + 1) * vCap) < tw ∧
      2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap) < tw ∧
      (L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap)) < tw ∧
      dsSGenBase b L vCap eCap < tw) ∧
    (dsHPtr b vCap eCap + 4 < tw ∧ dgEPresBase (dsHPtr b vCap eCap) vCap < tw) := by
  obtain ⟨hn, hh, hd, hm, hg, hH, ha, hdom, hsg, -, -, -, -⟩ :=
    stepPosNE_fixed_bases_lt_w b L vCap eCap tw h
  have e1 : dsGPtr b = b + 6 := rfl
  have e2 : dsHPtr b vCap eCap = dsGPtr b + (4 + 7 * vCap + 9 * eCap) := rfl
  have e2' : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have e3 : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have e4 : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have e5 : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have e6 : dsHHeadBase b vCap eCap = dsHNextBase b vCap eCap + 2 * eCap := by
    simp only [dsHHeadBase, dsHPrevBase]; ring
  have e7 : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have e8 : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  have e9 : dsSGenBase b L vCap eCap = dsDomGenBase b L vCap eCap +
      ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) := by
    simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; ring
  have e10 : dgEPresBase (dsHPtr b vCap eCap) vCap + 9 * eCap = dsAuxPtr b vCap eCap := by
    simp only [dgEPresBase, dsAuxPtr, dynGraphSize]; omega
  have e11 : dgEPresBase (dsHPtr b vCap eCap) vCap = dsHPtr b vCap eCap + 4 + 7 * vCap := rfl
  simp only [dsLOff, dsVCapOff, dsECapOff, dsHdrSize]
  rw [← e3, ← e4, ← e5, ← e6, ← e7, ← e8, ← e2']
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    hH, ha, hm, hn⟩, ⟨by omega, hh, by omega, hd, hdom⟩,
    ?_, by omega, by omega⟩
  rw [e9] at hsg
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Execute the 16 layout-setup assignments (`r6..r21`) at the top of `dsStepPosEmptyStmt`. -/
private lemma stepPosE_setup_regs {w L vCap eCap b retAff : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem regs : ℕ → ℕ} {pos k T : ℕ}
    {rest : Stmt} {Post : Outcome → State → Prop}
    (h16 : 16 < 2 ^ w) (hfix : b + dsFixedSize L vCap eCap < 2 ^ w)
    (huh : retAff + eCap < 2 ^ w)
    (hr0 : regs 0 = b) (hr3 : regs 3 = retAff)
    (hL : mem (b + dsLOff) = L) (hV : mem (b + dsVCapOff) = vCap) (hE : mem (b + dsECapOff) = eCap)
    (hcont : ∀ regs' : ℕ → ℕ,
      (∀ r ≤ 5, regs' r = regs r) →
      (regs' 6 = L ∧ regs' 7 = vCap ∧ regs' 8 = eCap ∧ regs' 10 = dsGPtr b ∧
       regs' 11 = dsHPtr b vCap eCap ∧ regs' 12 = dsAuxPtr b vCap eCap ∧
       regs' 13 = dsMinHBase b vCap eCap ∧ regs' 14 = dsHNextBase b vCap eCap ∧
       regs' 15 = dsHHeadBase b vCap eCap ∧ regs' 16 = dsHDegDummyBase b L vCap eCap ∧
       regs' 17 = dsDomGenBase b L vCap eCap ∧ regs' 18 = dsSGenBase b L vCap eCap ∧
       regs' 19 = dgEPresBase (dsHPtr b vCap eCap) vCap ∧ regs' 20 = L + 1 ∧
       regs' 21 = retAff + eCap) →
      ∃ o st' c, Runs w p ω rest { regs := regs', mem := mem, pos := pos } o st' c ∧
        Post o st' ∧ k + 150 + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 6 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 7 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 8 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 9 (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 7)) (.bin .mul (.const 9) (.reg 8)))) ;;
       .assign 10 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
       .assign 11 (.bin .add (.reg 10) (.reg 9)) ;;
       .assign 12 (.bin .add (.reg 11) (.reg 9)) ;;
       .assign 13 (.bin .add (.reg 12) (.reg 9)) ;;
       .assign 14 (.bin .add (.reg 13) (.reg 8)) ;;
       .assign 15 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 8))) ;;
       .assign 20 (.bin .add (.reg 6) (.const 1)) ;;
       .assign 16 (.bin .add (.reg 15) (.reg 20)) ;;
       .assign 17 (.bin .add (.reg 16) (.reg 20)) ;;
       .assign 18 (.bin .add (.reg 17)
         (.bin .add (.reg 20)
           (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 20) (.reg 8)))
             (.bin .mul (.const 2) (.bin .mul (.reg 20) (.reg 7)))))) ;;
       .assign 19 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 7))) ;;
       .assign 21 (.bin .add (.reg 3) (.reg 8)) ;;
       rest)
      { regs := regs, mem := mem, pos := pos } o st' c ∧ Post o st' ∧ k + c ≤ T := by
  have hc : ∀ n ≤ 16, n < 2 ^ w := fun _ hn => lt_of_le_of_lt hn h16
  have hdg : dynGraphSize vCap eCap = 4 + (7 * vCap + 9 * eCap) := by
    simp only [dynGraphSize]; ring
  have hhh : dsHHeadBase b vCap eCap = dsHNextBase b vCap eCap + 2 * eCap := by
    simp only [dsHHeadBase, dsHPrevBase]; ring
  have hsG : dsSGenBase b L vCap eCap = dsDomGenBase b L vCap eCap +
      ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) := by
    simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; ring
  have hhp : dgEPresBase (dsHPtr b vCap eCap) vCap = dsHPtr b vCap eCap + 4 + 7 * vCap := rfl
  obtain ⟨hB1, hB2, hB3, hB4⟩ := stepPosE_setup_bounds b L vCap eCap (2 ^ w) hfix
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (hc dsLOff (by decide))) hB1.1) hL) ?_
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (hc dsVCapOff (by decide))) hB1.2.1) hV) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (hc dsECapOff (by decide))) hB1.2.2.1) hE) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (by
      rw [hdg]
      exact Expr.eval_add (Expr.eval_const (hc 4 (by decide)))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (hc 7 (by decide))) (Expr.eval_reg_of_eq (by simp))
            hB1.2.2.2.1)
          (Expr.eval_mul (Expr.eval_const (hc 9 (by decide))) (Expr.eval_reg_of_eq (by simp))
            hB1.2.2.2.2.1)
          hB1.2.2.2.2.2.1) hB1.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsGPtr b)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (hc dsHdrSize (by decide))) hB1.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      hB1.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsAuxPtr b vCap eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      hB1.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      hB1.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsHNextBase b vCap eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      hB1.2.2.2.2.2.2.2.2.2.2.2) ?_
  refine runs_seq_assign_le (v := dsHHeadBase b vCap eCap)
    (by
      rw [hhh]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_mul (Expr.eval_const (hc 2 (by decide))) (Expr.eval_reg_of_eq (by simp))
          hB2.1) hB2.2.1) ?_
  refine runs_seq_assign_le (v := L + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (hc 1 (by decide)))
      hB2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsHDegDummyBase b L vCap eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      hB2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
      hB2.2.2.2.2) ?_
  refine runs_seq_assign_le (v := dsSGenBase b L vCap eCap)
    (by
      rw [hsG]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (hc 2 (by decide)))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
                hB3.1)
              hB3.2.2.1)
            (Expr.eval_mul (Expr.eval_const (hc 2 (by decide)))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
                hB3.2.1)
              hB3.2.2.2.1) hB3.2.2.2.2.1) hB3.2.2.2.2.2.1) (hsG ▸ hB3.2.2.2.2.2.2)) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap + 4 + 7 * vCap)
    (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (hc 4 (by decide)))
        hB4.1)
      (Expr.eval_mul (Expr.eval_const (hc 7 (by decide))) (Expr.eval_reg_of_eq (by simp))
        hB1.2.2.2.1)
      (hhp ▸ hB4.2)) ?_
  refine runs_seq_assign_le (v := retAff + eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr3])) (Expr.eval_reg_of_eq (by simp)) huh) ?_
  refine runs_cost_mono_e (hcont _
    (fun r hr => by
      simp only [Function.update_of_ne (show r ≠ 21 by omega),
        Function.update_of_ne (show r ≠ 19 by omega), Function.update_of_ne (show r ≠ 18 by omega),
        Function.update_of_ne (show r ≠ 17 by omega), Function.update_of_ne (show r ≠ 16 by omega),
        Function.update_of_ne (show r ≠ 20 by omega), Function.update_of_ne (show r ≠ 15 by omega),
        Function.update_of_ne (show r ≠ 14 by omega), Function.update_of_ne (show r ≠ 13 by omega),
        Function.update_of_ne (show r ≠ 12 by omega), Function.update_of_ne (show r ≠ 11 by omega),
        Function.update_of_ne (show r ≠ 10 by omega), Function.update_of_ne (show r ≠ 9 by omega),
        Function.update_of_ne (show r ≠ 8 by omega), Function.update_of_ne (show r ≠ 7 by omega),
        Function.update_of_ne (show r ≠ 6 by omega)])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
     by simp, by simp, by simp [dgEPresBase], by simp, by simp⟩) ?_
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
  omega

public section

/-- `dsStepPosEmptyStmt` meets `dsStepPosEmptyContract`. -/
theorem dsStepPosEmpty_meetsContract (ctx : StepPosEmptyCtx) {p : Program}
    {bs : StepPosNEBases} {bEm : ℕ} (hp : HasStepPosEmptyProcs p bs bEm) :
    MeetsContract ctx.w p (bEm + stepPosEmptyIdx) (dsStepPosEmptyContract ctx) := by
  refine meetsContract_of_runs
    (hp.hpEm.get (i := stepPosEmptyIdx) (by simp [stepPosEmptyProcs, stepPosEmptyIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, rfl⟩
  simp only [stepPosEmptyProcs, stepPosEmptyIdx, List.getElem_cons_zero]
  dsimp only [dsStepPosEmptyStmt]
  obtain ⟨hwb_fix, hwb_b, hwb_j1, hwb_L1, hwb_v, hwb_e, hwb_eAff, hwb_ret, hwb_uh1, hwb_dP,
    hwb_2obs, hwb_hs2, h16_lt⟩ := stepPosE_word_bounds ctx
  have hc_lt : ∀ n ≤ 16, n < 2 ^ ctx.w := fun _ hn => lt_of_le_of_lt hn h16_lt
  obtain ⟨hFB_g, hFB_h, _, hFB_mh, hFB_hn, hFB_hh, hFB_hd, hFB_dg, hFB_sg, hFB_hP, _, _⟩ :=
    stepPosE_fixed_lt ctx.b ctx.L ctx.vCap ctx.eCap (2 ^ ctx.w) hwb_fix
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hHdr_aff : ctx.memAff (ctx.b + dsLOff) = ctx.L ∧
      ctx.memAff (ctx.b + dsVCapOff) = ctx.vCap ∧
      ctx.memAff (ctx.b + dsECapOff) = ctx.eCap := by
    have hag : ∀ off, off < dsHdrSize → off ≠ dsGenOff →
        ctx.memAff (ctx.b + off) = ctx.mem0 (ctx.b + off) := fun off ho1 ho2 =>
      (ctx.hAff_frame (ctx.b + off) (by have := ctx.hfix_step; have := ctx.hhead_in; omega)
        (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega))).trans (ctx.hHdr_02 _ (by omega) (by simp [dsGPtr]; omega) (by omega))
    exact ⟨(hag dsLOff (by decide) (by decide)).trans ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (hag dsVCapOff (by decide) (by decide)).trans ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (hag dsECapOff (by decide) (by decide)).trans ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨c, r, hc_w, hc_e, hc_v, hc_lo, hc_hi, hc_out, hc_es, hc_size, hc_bk,
    hr_L, hr_v, hr_e, hr_b, hr_j, hr_es, hr_bk, hPermRecs, hApplyRecs, hDelIns,
    hminNew, hnewB, hFinPre⟩ := stepPosE_buildFinish ctx
  refine runs_cost_start_e ?_
  refine stepPosE_setup_regs h16_lt hwb_fix (Nat.lt_of_succ_lt hwb_uh1)
    (by simp) (by simp) hHdr_aff.1 hHdr_aff.2.1 hHdr_aff.2.2 ?_
  intro regs1 hR1_old hR1_new
  obtain ⟨h1_6, h1_7, h1_8, h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17, h1_18,
    h1_19, h1_20, h1_21⟩ := hR1_new
  have h1_0 : regs1 0 = ctx.b := (hR1_old 0 (by decide)).trans (by simp)
  have h1_1 : regs1 1 = ctx.j := (hR1_old 1 (by decide)).trans (by simp)
  have h1_2 : regs1 2 = ctx.eAffPtr := (hR1_old 2 (by decide)).trans (by simp)
  have h1_3 : regs1 3 = ctx.retAff := (hR1_old 3 (by decide)).trans (by simp)
  have h1_4 : regs1 4 = ctx.oldBucketsSum := (hR1_old 4 (by decide)).trans (by simp)
  have h1_5 : regs1 5 = ctx.heapStep := (hR1_old 5 (by decide)).trans (by simp)
  have hFinMC : MeetsContract ctx.w p (bs.bFin + stepFinishIdx)
      (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
        ctx.uhTailHdr r ctx.G' [] (fun _ => []) (fun _ => False)
        ctx.eAffPtr ctx.retAff ctx.uhTailHdr) :=
    hc_w ▸ dsStepFinish_meetsContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
      ctx.uhTailHdr r ctx.G' [] (fun _ => []) (fun _ => False)
      ctx.eAffPtr ctx.retAff ctx.uhTailHdr
      hp.hpDR hp.hpDA hp.hpOps hp.hpIR hp.hpUT hp.hpBatch hp.hpEdge hp.hpSplit hp.hpAU hp.hpUE
      hp.hpCB hp.hpPhase hp.hpFL hp.hpRB hp.hpSE hp.hpZ hp.hpClrA hp.hpST hp.hpLW hp.hpRev
      hp.hpFin
  refine runs_seq_call_le
    (vs := [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
      dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
      ctx.retAff, ctx.uhTailHdr + 1, ctx.retAff, 0,
      dgEPresBase (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap,
      dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, ctx.uhTailHdr] ++
     [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
      dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
      dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b, ctx.retAff, 0] ++
     [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
      ctx.j + 1, ctx.j, ctx.L + 1] ++
     [ctx.b, ctx.j, ctx.eAffPtr, 0, ctx.retAff, ctx.uhTailHdr])
    hFinMC
    (by
      simp only [List.cons_append, List.nil_append]
      exact evalArgs_cons (Expr.eval_reg_of_eq h1_14) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_15) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_16) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_20) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_3) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq h1_21)
          (Expr.eval_const (hc_lt 1 (by decide))) hwb_uh1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_3) <|
        evalArgs_cons (Expr.eval_const (hc_lt 0 (by decide))) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_19) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_10) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_11) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_21) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_14) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_15) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_16) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_20) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_13) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_0) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_3) <|
        evalArgs_cons (Expr.eval_const (hc_lt 0 (by decide))) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_17) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_18) <|
        evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq h1_1)
          (Expr.eval_const (hc_lt 1 (by decide))) hwb_j1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_20) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_0) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_1) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_2) <|
        evalArgs_cons (Expr.eval_const (hc_lt 0 (by decide))) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_3) <|
        evalArgs_cons (Expr.eval_reg_of_eq h1_21) <|
        evalArgs_nil _ _)
    (fun v hv => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      have hj_lt : ctx.j < 2 ^ ctx.w := Nat.lt_of_succ_lt hwb_j1
      have huh_lt : ctx.uhTailHdr < 2 ^ ctx.w := Nat.lt_of_succ_lt hwb_uh1
      have h0_lt : 0 < 2 ^ ctx.w := hc_lt 0 (by decide)
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · exact hFB_hn
      · exact hFB_hh
      · exact hFB_hd
      · exact hj_lt
      · exact hwb_L1
      · exact hwb_ret
      · exact hwb_uh1
      · exact hwb_ret
      · exact h0_lt
      · exact hFB_hP
      · exact hFB_g
      · exact hFB_h
      · exact huh_lt
      · exact hFB_hn
      · exact hFB_hh
      · exact hFB_hd
      · exact hj_lt
      · exact hwb_L1
      · exact hFB_mh
      · exact hwb_b
      · exact hwb_ret
      · exact h0_lt
      · exact hFB_dg
      · exact hFB_sg
      · exact hwb_j1
      · exact hj_lt
      · exact hwb_L1
      · exact hwb_b
      · exact hj_lt
      · exact hwb_eAff
      · exact h0_lt
      · exact hwb_ret
      · exact huh_lt)
    hFinPre ?_
  rintro retFin memFin posFin hFinPost
  refine runs_seq_assign_le (v := ctx.dPtr)
    (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_21]))
        (Expr.eval_const (hc_lt 1 (by decide))) hwb_uh1)
      (Expr.eval_mul (Expr.eval_const (hc_lt 2 (by decide)))
        (Expr.eval_reg_of_eq (by simp [h1_4])) hwb_2obs) hwb_dP) ?_
  refine runs_seq_store_le (x := ctx.heapStep) (v := ctx.uhTailHdr)
    (Expr.eval_reg_of_eq (by simp [h1_5])) (Expr.eval_reg_of_eq (by simp [h1_21])) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 1) (v := ctx.dPtr)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_5]))
      (Expr.eval_const (hc_lt 1 (by decide))) (Nat.lt_of_succ_lt hwb_hs2))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := ctx.heapStep + 2) (v := 0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h1_5]))
      (Expr.eval_const (hc_lt 2 (by decide))) hwb_hs2)
    (Expr.eval_const (hc_lt 0 (by decide))) ?_
  have hMid := stepPosE_midPost ctx
    ⟨hc_w, hc_e, hc_v, hc_lo, hc_hi, hc_out, hc_es, hc_size⟩
    ⟨hr_L, hr_v, hr_e, hr_b, hr_j, hr_es⟩ hPermRecs hApplyRecs hDelIns hminNew hnewB hFinPost
    rfl
  refine runs_ret_le (v := ctx.dPtr) (Expr.eval_reg_of_eq (by simp)) ⟨hMid, rfl⟩ ?_
  dsimp only [dsStepPosEmptyContract, dsStepPosEmptyCost, dsStepFinishContract]
  rw [hc_bk, hr_bk]
  simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, argsSize_cons, argsSize_nil,
    hc_lo, hc_hi, hr_L, hr_j, hc_es, hr_es, hc_size, List.length_nil, List.map_nil, List.sum_nil]
  omega

end

end MinCostFlow.DynSpanner.Program
