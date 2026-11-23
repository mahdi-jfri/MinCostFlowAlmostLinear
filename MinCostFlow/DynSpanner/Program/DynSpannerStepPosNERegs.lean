module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueC

/-!
# The nonempty `E_aff` branch of a `0 < j` step: contract and register setup

Defines `dsStepPosNonEmptyContract`, the contract of `dsStepPosNonEmptyStmt`
(`DynSpannerStepPosNonEmptyDefs.lean`), and proves the lemmas that run its straight-line parts:
the word-size bounds, the assignments that compute the addresses of the state block, and the
registers passed to `dsStepFinish`.
-/

public section

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] noncomputable def dsStepPosNonEmptyContract (ctx : StepPosNECtx) : Contract where
  pre args mem :=
    args = [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.wpPtr, ctx.cand.length,
      ctx.oldBucketsSum, ctx.heapStep] ∧
    mem = ctx.memAff
  post _ _ ret mem' :=
    StepPosMidPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.mem2 ctx.x ctx.headHeap ctx.r₁ ctx.heapStep ctx.heapAff ctx.sPrevList
      ctx.prefWords mem' ret ∧
    ret ≤ dsStepPosNonEmptyEnd ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.G' ctx.J
      ctx.piLt_mid ctx.embJH ctx.eAff ctx.wpPtr ctx.cand.length ctx.oldBucketsSum ∧
    ListAt mem' ctx.eAffPtr ctx.eAff ∧
    ctx.eAffPtr + ctx.eAff.length ≤ ret
  cost _ _ :=
    dsStepPosNonEmptyCost ctx.impl ctx.mMax ctx.L ctx.vCap ctx.eCap ctx.j ctx.G' ctx.J
      ctx.piLt_mid ctx.embJH ctx.S_prev ctx.eAff ctx.oldBucketsSum

/-- Word-size bounds needed by `eval_expr` inside `dsStepPosNonEmptyStmt`. -/
lemma stepPosNE_word_bounds (ctx : StepPosNECtx) :
    ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap < 2 ^ ctx.w ∧
    ctx.guestBase < 2 ^ ctx.w ∧
    ctx.wpPtr + ctx.eAff.length < 2 ^ ctx.w ∧
    ctx.lenSum < 2 ^ ctx.w ∧
    ctx.J.n < 2 ^ ctx.w ∧
    ctx.j + 1 < 2 ^ ctx.w ∧
    ctx.L + 1 < 2 ^ ctx.w ∧
    ctx.vCap < 2 ^ ctx.w ∧
    ctx.eCap < 2 ^ ctx.w ∧
    ctx.b + dsLOff < 2 ^ ctx.w ∧
    ctx.b + dsVCapOff < 2 ^ ctx.w ∧
    ctx.b + dsECapOff < 2 ^ ctx.w ∧
    ctx.b + dsGenOff < 2 ^ ctx.w ∧
    dsAuxPtr ctx.b ctx.vCap ctx.eCap + dgNOff < 2 ^ ctx.w ∧
    16 < 2 ^ ctx.w := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  have hgo := genOff_lt_hPtr ctx.b ctx.L ctx.vCap ctx.eCap
  have hjle : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hsp := spOutBound_lt_of_end ctx.hEnd_ltw
  have hgb_lt : ctx.guestBase < 2 ^ ctx.w := hsp.2.2.1
  have hdg_n : dgNOff = 2 := rfl
  have hdg_ge : 4 ≤ dynGraphSize ctx.vCap ctx.eCap := by
    simp only [dynGraphSize]; omega
  have hOffs : dsLOff = 2 ∧ dsVCapOff = 3 ∧ dsECapOff = 4 ∧ dsHdrSize = 6 :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hb1 : 1 ≤ ctx.b := ctx.hState.2.2.2.1
  dsimp only [StepPosNECtx.guestBase, StepPosNECtx.scratchPtr] at hgb_lt ⊢
  omega

lemma stepPosNE_runs_cost_start {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ 0 + c ≤ T) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ c ≤ T := by
  simpa only [zero_add] using h

private lemma stepPosNE_runs_cost_mono {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {k₁ k₂ T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k₂ + c ≤ T) (hle : k₁ ≤ k₂) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k₁ + c ≤ T := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', c, hr, hq, by omega⟩

/-- First 9 header/layout assignment steps (`r8..r16`). -/
lemma stepPosNE_hdr_a {w b L vCap eCap k T : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {s : Stmt} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hr0 : st.regs 0 = b)
    (hmL : st.mem (b + dsLOff) = L)
    (hmV : st.mem (b + dsVCapOff) = vCap)
    (hmE : st.mem (b + dsECapOff) = eCap)
    (hrest : ∀ regs' : ℕ → ℕ,
      (∀ r, r < 8 → regs' r = st.regs r) →
      regs' 8 = L ∧ regs' 9 = vCap ∧ regs' 10 = eCap ∧
      regs' 11 = dynGraphSize vCap eCap ∧
      regs' 12 = dsGPtr b ∧ regs' 13 = dsHPtr b vCap eCap ∧
      regs' 14 = dsAuxPtr b vCap eCap ∧ regs' 15 = dsMinHBase b vCap eCap ∧
      regs' 16 = dsHNextBase b vCap eCap →
      ∃ o st' c, Runs w p ω s { st with regs := regs' } o st' c ∧ Q o st' ∧ (k + 65) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 8 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 9 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 10 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 11 (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 9)) (.bin .mul (.const 9) (.reg 10)))) ;;
       .assign 12 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
       .assign 13 (.bin .add (.reg 12) (.reg 11)) ;;
       .assign 14 (.bin .add (.reg 13) (.reg 11)) ;;
       .assign 15 (.bin .add (.reg 14) (.reg 11)) ;;
       .assign 16 (.bin .add (.reg 15) (.reg 10)) ;; s)
      st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have hfl := fixed_layout_order b L vCap eCap
  have hdg : dynGraphSize vCap eCap = 4 + (7 * vCap + 9 * eCap) := by
    simp only [dynGraphSize]; ring
  have hhn : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hB :
      b + dsLOff < 2 ^ w ∧ b + dsVCapOff < 2 ^ w ∧ b + dsECapOff < 2 ^ w ∧
      7 * vCap < 2 ^ w ∧ 9 * eCap < 2 ^ w ∧ 7 * vCap + 9 * eCap < 2 ^ w ∧
      4 + (7 * vCap + 9 * eCap) < 2 ^ w ∧
      b + dsHdrSize < 2 ^ w ∧ dsGPtr b + dynGraphSize vCap eCap < 2 ^ w ∧
      dsHPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w ∧
      dsAuxPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w ∧
      dsMinHBase b vCap eCap + eCap < 2 ^ w := by
    simp only [dsLOff, dsVCapOff, dsECapOff, dsHdrSize] at hfl ⊢; omega
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by simp only [dsLOff]; omega)) hB.1) hmL) ?_
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (by simp only [dsVCapOff]; omega)) hB.2.1) hmV) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (by simp only [dsECapOff]; omega)) hB.2.2.1) hmE) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (by
      rw [hdg]
      exact Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.1)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.1)
          hB.2.2.2.2.2.1) hB.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsGPtr b)
    (by
      rw [← hfl.1]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
        (Expr.eval_const (by simp only [dsHdrSize]; omega)) hB.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap)
    (by
      rw [← hfl.2.1]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsAuxPtr b vCap eCap)
    (by
      rw [← hfl.2.2.1]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (by
      rw [← hfl.2.2.2.1]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsHNextBase b vCap eCap)
    (by
      rw [hhn]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.2.2.2.2.2.2.2) ?_
  refine stepPosNE_runs_cost_mono (hrest _ (fun r hr => by
      simp only [Function.update_of_ne (show r ≠ 16 by omega),
        Function.update_of_ne (show r ≠ 15 by omega), Function.update_of_ne (show r ≠ 14 by omega),
        Function.update_of_ne (show r ≠ 13 by omega), Function.update_of_ne (show r ≠ 12 by omega),
        Function.update_of_ne (show r ≠ 11 by omega), Function.update_of_ne (show r ≠ 10 by omega),
        Function.update_of_ne (show r ≠ 9 by omega), Function.update_of_ne (show r ≠ 8 by omega)])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩) ?_
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
  omega

/-- Next 8 header/layout assignment steps (`r17, r40, r18..r23`). -/
lemma stepPosNE_hdr_b {w b L vCap eCap k T : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {s : Stmt} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w)
    (hfix : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hr8 : st.regs 8 = L) (hr9 : st.regs 9 = vCap) (hr10 : st.regs 10 = eCap)
    (hr16 : st.regs 16 = dsHNextBase b vCap eCap)
    (hrest : ∀ regs' : ℕ → ℕ,
      (∀ r, r < 17 → regs' r = st.regs r) →
      regs' 17 = dsHHeadBase b vCap eCap ∧
      regs' 18 = dsHDegDummyBase b L vCap eCap ∧ regs' 19 = dsDomGenBase b L vCap eCap ∧
      regs' 20 = dsSGenBase b L vCap eCap ∧ regs' 21 = dsSBitBase b L vCap eCap ∧
      regs' 22 = dsEStampBase b L vCap eCap ∧ regs' 23 = dsMEmbTempBase b L vCap eCap ∧
      regs' 40 = L + 1 →
      ∃ o st' c, Runs w p ω s { st with regs := regs' } o st' c ∧ Q o st' ∧ (k + 75) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 17 (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 10))) ;;
       .assign 40 (.bin .add (.reg 8) (.const 1)) ;;
       .assign 18 (.bin .add (.reg 17) (.reg 40)) ;;
       .assign 19 (.bin .add (.reg 18) (.reg 40)) ;;
       .assign 20 (.bin .add (.reg 19)
         (.bin .add (.reg 40)
           (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 40) (.reg 10)))
             (.bin .mul (.const 2) (.bin .mul (.reg 40) (.reg 9)))))) ;;
       .assign 21 (.bin .add (.reg 20)
         (.bin .add (.bin .mul (.const 2) (.reg 40)) (.bin .mul (.reg 40) (.reg 9)))) ;;
       .assign 22 (.bin .add (.reg 21) (.bin .mul (.const 2) (.reg 9))) ;;
       .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 10))) ;; s)
      st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have hfl := fixed_layout_order b L vCap eCap
  have h1 : dsHHeadBase b vCap eCap = dsHNextBase b vCap eCap + 2 * eCap := by
    simp only [dsHHeadBase, dsHPrevBase]; ring
  have h2 : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have h3 : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  have h4 : dsSGenBase b L vCap eCap = dsDomGenBase b L vCap eCap +
      ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) := by
    simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; ring
  have h5 : dsSBitBase b L vCap eCap = dsSGenBase b L vCap eCap +
      (2 * (L + 1) + (L + 1) * vCap) := by
    simp only [dsSBitBase, dsSHeadBase, dsVSGenBase]; ring
  have h6 : dsEStampBase b L vCap eCap = dsSBitBase b L vCap eCap + 2 * vCap := by
    simp only [dsEStampBase, dsVStampBase]; ring
  have h7 : dsMEmbTempBase b L vCap eCap = dsEStampBase b L vCap eCap + 2 * eCap := by
    simp only [dsMEmbTempBase, dsKeptStampBase]; ring
  have hhn : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hB :
      2 * eCap < 2 ^ w ∧ dsHNextBase b vCap eCap + 2 * eCap < 2 ^ w ∧
      L + 1 < 2 ^ w ∧ dsHHeadBase b vCap eCap + (L + 1) < 2 ^ w ∧
      dsHDegDummyBase b L vCap eCap + (L + 1) < 2 ^ w ∧
      (L + 1) * eCap < 2 ^ w ∧ 2 * ((L + 1) * eCap) < 2 ^ w ∧
      (L + 1) * vCap < 2 ^ w ∧ 2 * ((L + 1) * vCap) < 2 ^ w ∧
      2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap) < 2 ^ w ∧
      (L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap)) < 2 ^ w ∧
      dsDomGenBase b L vCap eCap + ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) < 2 ^ w ∧
      2 * (L + 1) < 2 ^ w ∧ 2 * (L + 1) + (L + 1) * vCap < 2 ^ w ∧
      dsSGenBase b L vCap eCap + (2 * (L + 1) + (L + 1) * vCap) < 2 ^ w ∧
      2 * vCap < 2 ^ w ∧ dsSBitBase b L vCap eCap + 2 * vCap < 2 ^ w ∧
      dsEStampBase b L vCap eCap + 2 * eCap < 2 ^ w := by omega
  refine runs_seq_assign_le (v := dsHHeadBase b vCap eCap)
    (by
      rw [h1]
      exact Expr.eval_add (Expr.eval_reg_of_eq hr16)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr10) hB.1) hB.2.1) ?_
  refine runs_seq_assign_le (v := L + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr8])) (Expr.eval_const (by omega)) hB.2.2.1) ?_
  refine runs_seq_assign_le (v := dsHDegDummyBase b L vCap eCap)
    (by
      rw [h2]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (by
      rw [h3]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp)) hB.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsSGenBase b L vCap eCap)
    (by
      rw [h4]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [hr10]))
                hB.2.2.2.2.2.1) hB.2.2.2.2.2.2.1)
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [hr9]))
                hB.2.2.2.2.2.2.2.1) hB.2.2.2.2.2.2.2.2.1)
            hB.2.2.2.2.2.2.2.2.2.1) hB.2.2.2.2.2.2.2.2.2.2.1) hB.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsSBitBase b L vCap eCap)
    (by
      rw [h5]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
            hB.2.2.2.2.2.2.2.2.2.2.2.2.1)
          (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [hr9]))
            hB.2.2.2.2.2.2.2.1) hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsEStampBase b L vCap eCap)
    (by
      rw [h6]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr9]))
          hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dsMEmbTempBase b L vCap eCap)
    (by
      rw [h7]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr10])) hB.1)
        hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) ?_
  refine stepPosNE_runs_cost_mono (hrest _ (fun r hr => by
      simp only [Function.update_of_ne (show r ≠ 23 by omega),
        Function.update_of_ne (show r ≠ 22 by omega), Function.update_of_ne (show r ≠ 21 by omega),
        Function.update_of_ne (show r ≠ 20 by omega), Function.update_of_ne (show r ≠ 19 by omega),
        Function.update_of_ne (show r ≠ 18 by omega), Function.update_of_ne (show r ≠ 40 by omega),
        Function.update_of_ne (show r ≠ 17 by omega)])
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩) ?_
  simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]
  omega

lemma stepPosNE_fixed_bases_lt_w (b L vCap eCap tw : ℕ) (h : b + dsFixedSize L vCap eCap < tw) :
    dsHNextBase b vCap eCap < tw ∧ dsHHeadBase b vCap eCap < tw ∧
    dsHDegDummyBase b L vCap eCap < tw ∧ dsMinHBase b vCap eCap < tw ∧
    dsGPtr b < tw ∧ dsHPtr b vCap eCap < tw ∧ dsAuxPtr b vCap eCap < tw ∧
    dsDomGenBase b L vCap eCap < tw ∧ dsSGenBase b L vCap eCap < tw ∧
    dsSBitBase b L vCap eCap < tw ∧ dsEStampBase b L vCap eCap < tw ∧
    dsMEmbTempBase b L vCap eCap < tw ∧ b < tw := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ :=
    fixed_layout_order b L vCap eCap
  have h1 : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have h2 : dsHHeadBase b vCap eCap = dsHNextBase b vCap eCap + eCap + eCap := rfl
  have h3 : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  have h4 : dsDomGenBase b L vCap eCap = dsHDegDummyBase b L vCap eCap + (L + 1) := rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Seven register-setup assignments (`r33..r39`) right before `dsStepFinish`. -/
lemma stepPosNE_fin_regs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos k T : ℕ}
    {vCap eCap eLen lenSum retSp retReemb jtPtr jtM hPtr : ℕ}
    {rest : Stmt} {Post : Outcome → State → Prop}
    (h16 : 16 < 2 ^ w)
    (hr3 : regs 3 = eLen) (hr9 : regs 9 = vCap) (hr10 : regs 10 = eCap)
    (hr13 : regs 13 = hPtr) (hr24 : regs 24 = lenSum) (hr29 : regs 29 = jtPtr)
    (hr31 : regs 31 = retSp + eCap) (hr32 : regs 32 = retReemb)
    (hjtM : mem (jtPtr + dgMOff) = jtM)
    (hret_le : retReemb < 2 ^ w)
    (hMid :
      let reembDelta := retReemb - (retSp + eCap)
      let heapFin := retSp + eCap + 16 * eLen + 14 * lenSum + 3 * reembDelta
      let uhTailHdr := heapFin + 2 * reembDelta
      heapFin < 2 ^ w ∧ uhTailHdr < 2 ^ w ∧ jtPtr + dgMOff < 2 ^ w ∧
      dgEPresBase jtPtr vCap < 2 ^ w ∧ dgEListBase jtPtr vCap eCap < 2 ^ w ∧
      dgEPresBase hPtr vCap < 2 ^ w ∧ 16 * eLen < 2 ^ w ∧ 14 * lenSum < 2 ^ w ∧
      3 * reembDelta < 2 ^ w ∧ 14 * lenSum + 3 * reembDelta < 2 ^ w ∧
      16 * eLen + (14 * lenSum + 3 * reembDelta) < 2 ^ w ∧ 2 * reembDelta < 2 ^ w ∧
      jtPtr + 4 < 2 ^ w ∧ 7 * vCap < 2 ^ w ∧ hPtr + 4 < 2 ^ w)
    (hcont : ∀ regs' : ℕ → ℕ,
      (∀ r, (r ≤ 32 ∨ r = 40) → regs' r = regs r) →
      (let reembDelta := retReemb - (retSp + eCap)
       let heapFin := retSp + eCap + 16 * eLen + 14 * lenSum + 3 * reembDelta
       let uhTailHdr := heapFin + 2 * reembDelta
       regs' 33 = reembDelta ∧ regs' 34 = heapFin ∧ regs' 35 = uhTailHdr ∧
       regs' 36 = jtM ∧ regs' 37 = dgEPresBase jtPtr vCap ∧
       regs' 38 = dgEListBase jtPtr vCap eCap ∧ regs' 39 = dgEPresBase hPtr vCap) →
      ∃ o st' c, Runs w p ω rest { regs := regs', mem := mem, pos := pos } o st' c ∧
        Post o st' ∧ k + 66 + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 33 (.bin .sub (.reg 32) (.reg 31)) ;;
       .assign 34 (.bin .add (.reg 31)
         (.bin .add (.bin .mul (.const 16) (.reg 3))
           (.bin .add (.bin .mul (.const 14) (.reg 24)) (.bin .mul (.const 3) (.reg 33))))) ;;
       .assign 35 (.bin .add (.reg 34) (.bin .mul (.const 2) (.reg 33))) ;;
       .assign 36 (.load (.bin .add (.reg 29) (.const dgMOff))) ;;
       .assign 37 (.bin .add (.bin .add (.reg 29) (.const 4)) (.bin .mul (.const 7) (.reg 9))) ;;
       .assign 38 (.bin .add (.reg 37) (.reg 10)) ;;
       .assign 39 (.bin .add (.bin .add (.reg 13) (.const 4)) (.bin .mul (.const 7) (.reg 9))) ;;
       rest)
      { regs := regs, mem := mem, pos := pos } o st' c ∧ Post o st' ∧ k + c ≤ T := by
  have hc_lt : ∀ n ≤ 16, n < 2 ^ w := fun _ hn => lt_of_le_of_lt hn h16
  let reembDelta := retReemb - (retSp + eCap)
  let heapFin := retSp + eCap + 16 * eLen + 14 * lenSum + 3 * reembDelta
  let uhTailHdr := heapFin + 2 * reembDelta
  refine runs_seq_assign_le (v := reembDelta)
    (Expr.eval_sub (Expr.eval_reg_of_eq hr32) (Expr.eval_reg_of_eq hr31) hret_le) ?_
  refine runs_seq_assign_le (v := heapFin)
    (by
      have h1 : heapFin = (retSp + eCap) + (16 * eLen + (14 * lenSum + 3 * reembDelta)) := by
        dsimp only [heapFin]; omega
      rw [h1]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr31]))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (hc_lt 16 (by decide)))
            (Expr.eval_reg_of_eq (by simp [hr3])) hMid.2.2.2.2.2.2.1)
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (hc_lt 14 (by decide)))
              (Expr.eval_reg_of_eq (by simp [hr24])) hMid.2.2.2.2.2.2.2.1)
            (Expr.eval_mul (Expr.eval_const (hc_lt 3 (by decide)))
              (Expr.eval_reg_of_eq (by simp)) hMid.2.2.2.2.2.2.2.2.1)
            hMid.2.2.2.2.2.2.2.2.2.1) hMid.2.2.2.2.2.2.2.2.2.2.1) (h1 ▸ hMid.1)) ?_
  refine runs_seq_assign_le (v := uhTailHdr)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_mul (Expr.eval_const (hc_lt 2 (by decide)))
        (Expr.eval_reg_of_eq (by simp)) hMid.2.2.2.2.2.2.2.2.2.2.2.1) hMid.2.1) ?_
  refine runs_seq_assign_le (v := jtM)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr29]))
      (Expr.eval_const (hc_lt dgMOff (by decide))) hMid.2.2.1) hjtM) ?_
  refine runs_seq_assign_le (v := dgEPresBase jtPtr vCap)
    (by
      dsimp only [dgEPresBase]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr29]))
          (Expr.eval_const (hc_lt 4 (by decide))) hMid.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (Expr.eval_mul (Expr.eval_const (hc_lt 7 (by decide)))
          (Expr.eval_reg_of_eq (by simp [hr9])) hMid.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hMid.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dgEListBase jtPtr vCap eCap)
    (by
      dsimp only [dgEListBase]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [dgEPresBase]))
        (Expr.eval_reg_of_eq (by simp [hr10])) hMid.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dgEPresBase hPtr vCap)
    (by
      dsimp only [dgEPresBase]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr13]))
          (Expr.eval_const (hc_lt 4 (by decide))) hMid.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
        (Expr.eval_mul (Expr.eval_const (hc_lt 7 (by decide)))
          (Expr.eval_reg_of_eq (by simp [hr9])) hMid.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        hMid.2.2.2.2.2.1) ?_
  refine stepPosNE_runs_cost_mono (hcont _
    (fun r hr => by
      simp only [Function.update_of_ne (show r ≠ 39 by omega),
        Function.update_of_ne (show r ≠ 38 by omega), Function.update_of_ne (show r ≠ 37 by omega),
        Function.update_of_ne (show r ≠ 36 by omega), Function.update_of_ne (show r ≠ 35 by omega),
        Function.update_of_ne (show r ≠ 34 by omega), Function.update_of_ne (show r ≠ 33 by omega)])
    ⟨by simp [reembDelta], by simp [heapFin, reembDelta], by simp [uhTailHdr, heapFin, reembDelta],
     by simp, by simp, by simp, by simp⟩) ?_
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
  omega

end MinCostFlow.DynSpanner.Program
