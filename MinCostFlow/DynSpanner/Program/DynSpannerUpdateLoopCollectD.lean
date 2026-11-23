module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopAux
import Mathlib.Tactic.Ring

/-!
# Verification of batch `D`-collection (`DynSpannerUpdateLoopCollectD`)

Proves `dsCollectBatchD_meetsContract`: `dsCollectBatchDStmt` meets `dsCollectBatchDContract` in
`60 * (∑ i, |D_i|) + 80 * m + 250` steps, computing a duplicate-free list of
`(⋃ i < m, D_i) ∩ H.E` using a single bump of `mem[b + dsGenOff]` and `eStamp`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

/-! ## Setup phase (`r4..r17` and `dsGenOff` bump) -/

private lemma collectD_setup_bounds {w b L vCap eCap : ℕ}
    (hfw : b + dsFixedSize L vCap eCap < 2 ^ w) :
    b + dsLOff < 2 ^ w ∧ b + dsVCapOff < 2 ^ w ∧ b + dsECapOff < 2 ^ w ∧ b + dsGenOff < 2 ^ w ∧
    L + 1 < 2 ^ w ∧ 7 * vCap < 2 ^ w ∧ 9 * eCap < 2 ^ w ∧
    7 * vCap + 9 * eCap < 2 ^ w ∧ dynGraphSize vCap eCap < 2 ^ w ∧
    dsGPtr b < 2 ^ w ∧ dsGPtr b + 4 < 2 ^ w ∧ dgEPresBase (dsGPtr b) vCap < 2 ^ w ∧
    dsHPtr b vCap eCap < 2 ^ w ∧
    dsHPtr b vCap eCap + 4 < 2 ^ w ∧
    dgEPresBase (dsHPtr b vCap eCap) vCap < 2 ^ w ∧
    dsAuxPtr b vCap eCap < 2 ^ w ∧ dsMinHBase b vCap eCap < 2 ^ w ∧
    3 * eCap < 2 ^ w ∧ 2 * (L + 1) < 2 ^ w ∧ 3 * eCap + 2 * (L + 1) < 2 ^ w ∧
    dsDomGenBase b L vCap eCap < 2 ^ w ∧
    (L + 1) * eCap < 2 ^ w ∧ 2 * ((L + 1) * eCap) < 2 ^ w ∧
    (L + 1) * vCap < 2 ^ w ∧ 2 * ((L + 1) * vCap) < 2 ^ w ∧
    2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap) < 2 ^ w ∧
    (L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap)) < 2 ^ w ∧
    dsSGenBase b L vCap eCap < 2 ^ w ∧
    2 * (L + 1) + (L + 1) * vCap < 2 ^ w ∧ 2 * vCap < 2 ^ w ∧
    (2 * (L + 1) + (L + 1) * vCap) + 2 * vCap < 2 ^ w ∧
    dsEStampBase b L vCap eCap < 2 ^ w := by
  have heSt_lt : dsEStampBase b L vCap eCap < 2 ^ w := by
    have hcb := collectD_lt_eStamp_bounds b L vCap eCap
    have hA := hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hB := hcb.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    clear hcb; omega
  have hbL : b + dsLOff < 2 ^ w := by
    have hlt := (stepZero_fixed_lt b L vCap eCap).1 dsLOff (by decide); omega
  have hbV : b + dsVCapOff < 2 ^ w := by
    have hlt := (stepZero_fixed_lt b L vCap eCap).1 dsVCapOff (by decide); omega
  have hbE : b + dsECapOff < 2 ^ w := by
    have hlt := (stepZero_fixed_lt b L vCap eCap).1 dsECapOff (by decide); omega
  have hbG : b + dsGenOff < 2 ^ w := by
    have hlt := (stepZero_fixed_lt b L vCap eCap).1 dsGenOff (by decide); omega
  have hG_eq : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := rfl
  have hH_eq : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := rfl
  have hA_eq : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl
  have hM_eq : dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) = dsDomGenBase b L vCap eCap := by
    simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]; omega
  have hD_eq : dsDomGenBase b L vCap eCap + ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) =
      dsSGenBase b L vCap eCap := by
    simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega
  have hS_eq : dsSGenBase b L vCap eCap + ((2 * (L + 1) + (L + 1) * vCap) + 2 * vCap) =
      dsEStampBase b L vCap eCap := by
    simp only [dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase]; omega
  have hdg : dynGraphSize vCap eCap = 4 + (7 * vCap + 9 * eCap) := by simp [dynGraphSize]; omega
  have hgp : dgEPresBase (dsGPtr b) vCap = (dsGPtr b + 4) + 7 * vCap := by simp [dgEPresBase]
  have hhp : dgEPresBase (dsHPtr b vCap eCap) vCap = (dsHPtr b vCap eCap + 4) + 7 * vCap := by
    simp [dgEPresBase]
  clear hfw
  refine ⟨hbL, hbV, hbE, hbG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, heSt_lt⟩ <;> omega

private lemma collectD_setup_eqs (b L vCap eCap : ℕ) :
    4 + (7 * vCap + 9 * eCap) = dynGraphSize vCap eCap ∧
    b + dsHdrSize = dsGPtr b ∧
    (dsGPtr b + 4) + 7 * vCap = dgEPresBase (dsGPtr b) vCap ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    (dsHPtr b vCap eCap + 4) + 7 * vCap = dgEPresBase (dsHPtr b vCap eCap) vCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) =
      dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + ((2 * (L + 1) + (L + 1) * vCap) + 2 * vCap) =
      dsEStampBase b L vCap eCap := by
  refine ⟨by simp [dynGraphSize]; omega, rfl, by simp [dgEPresBase], rfl, by simp [dgEPresBase],
    rfl, rfl,
    by simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]; omega,
    by simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega,
    by simp only [dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase]; omega⟩

private lemma collectD_setup_triple (c : CollectDCtx) {p : Program} :
    Triple c.w p
      (fun st => st.mem = c.mem0 ∧ st.regs 0 = c.b ∧ st.regs 1 = c.stepHdrsPtr ∧
        st.regs 2 = c.m ∧ st.regs 3 = c.dOutPtr ∧ st.regs 4 = if c.isReemb then 1 else 0)
      dsCollectBatchDSetupStmt
      (normalPost fun st =>
        st.mem = Function.update c.mem0 (c.b + dsGenOff) (c.mem0 (c.b + dsGenOff) + 1) ∧
        st.regs 0 = c.b ∧ st.regs 1 = c.stepHdrsPtr ∧ st.regs 2 = c.m ∧ st.regs 3 = c.dOutPtr ∧
        st.regs 11 = dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap ∧
        st.regs 15 = dsEStampBase c.b c.L c.vCap c.eCap ∧
        st.regs 16 = c.mem0 (c.b + dsGenOff) + 1 ∧ st.regs 17 = 0 ∧
        st.regs 27 = (if c.isReemb then 5 else 3) ∧
        st.regs 28 = (if c.isReemb then 6 else 4))
      (fun _ => 210) := by
  intro st ω ⟨hm, r0, r1, r2, r3, r4⟩
  rcases st with ⟨mem_s, regs_s, pos_s⟩
  dsimp only at hm r0 r1 r2 r3 r4 ⊢
  subst mem_s
  have h16 := c.hw16
  obtain ⟨hbL, hbV, hbE, hbG, hL1, h7v, h9e, h7v9e, hdgW, hgPW, hgP4W, hgPresW, hhPW, hhP4W,
    hhPresW, hauxW, hminW, h3e, h2L1, h3e2L1, hdomW, hLe, h2Le, hLv, h2Lv, h2Le2Lv, hdomOff,
    hsGenW, h2L1Lv, h2v, hsOff, heStW⟩ := collectD_setup_bounds c.hfix_w
  obtain ⟨edg, egP, egPres, ehP, ehPres, eaux, emin, edom, esGen, eeSt⟩ :=
    collectD_setup_eqs c.b c.L c.vCap c.eCap
  dsimp only [dsCollectBatchDSetupStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := c.L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0)
      (Expr.eval_const (by simp [dsLOff]; omega)) hbL) c.hL) ?_
  refine runs_seq_assign_le (v := c.vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := c.b) (by simp [r0]))
      (Expr.eval_const (by simp [dsVCapOff]; omega)) hbV) c.hvC) ?_
  refine runs_seq_assign_le (v := c.eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := c.b) (by simp [r0]))
      (Expr.eval_const (by simp [dsECapOff]; omega)) hbE) c.heC) ?_
  refine runs_seq_assign_le (v := c.L + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := c.L) (by simp)) (Expr.eval_const (by omega)) hL1) ?_
  refine runs_seq_assign_le (v := dynGraphSize c.vCap c.eCap)
    (edg ▸ Expr.eval_add (Expr.eval_const (by omega))
      (Expr.eval_add
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := c.vCap) (by simp)) h7v)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := c.eCap) (by simp)) h9e)
        h7v9e)
      (edg.symm ▸ hdgW)) ?_
  refine runs_seq_assign_le (v := dsGPtr c.b)
    (egP ▸ Expr.eval_add (Expr.eval_reg_of_eq (v := c.b) (by simp [r0]))
      (Expr.eval_const (by simp [dsHdrSize]; omega)) (egP.symm ▸ hgPW)) ?_
  refine runs_seq_assign_le (v := dsHPtr c.b c.vCap c.eCap)
    (ehP ▸ Expr.eval_add (Expr.eval_reg_of_eq (v := dsGPtr c.b) (by simp))
      (Expr.eval_reg_of_eq (v := dynGraphSize c.vCap c.eCap) (by simp)) (ehP.symm ▸ hhPW)) ?_
  -- Branch on `r4 = if c.isReemb then 1 else 0` to set `r11`, `r27`, `r28`
  have hcond : ∀ (k0 : ℕ) (regs1 : ℕ → ℕ),
      regs1 0 = c.b → regs1 1 = c.stepHdrsPtr → regs1 2 = c.m → regs1 3 = c.dOutPtr →
      regs1 4 = (if c.isReemb then 1 else 0) →
      regs1 5 = c.vCap → regs1 6 = c.eCap → regs1 7 = c.L + 1 →
      regs1 8 = dynGraphSize c.vCap c.eCap → regs1 9 = dsGPtr c.b →
      regs1 10 = dsHPtr c.b c.vCap c.eCap →
      k0 + 165 ≤ 210 →
      ∃ o st' c0, Runs c.w p ω
        (.cond (.reg 4)
           (.assign 11 (.bin .add (.bin .add (.reg 9) (.const 4)) (.bin .mul (.const 7) (.reg 5))) ;;
            .assign 27 (.const 5) ;;
            .assign 28 (.const 6))
           (.assign 11 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 5))) ;;
            .assign 27 (.const 3) ;;
            .assign 28 (.const 4)) ;;
         .assign 12 (.bin .add (.bin .add (.reg 10) (.reg 8)) (.reg 8)) ;;
         .assign 13 (.bin .add (.reg 12)
           (.bin .add (.bin .mul (.const 3) (.reg 6)) (.bin .mul (.const 2) (.reg 7)))) ;;
         .assign 14 (.bin .add (.reg 13)
           (.bin .add (.reg 7)
             (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 7) (.reg 6)))
               (.bin .mul (.const 2) (.bin .mul (.reg 7) (.reg 5)))))) ;;
         .assign 15 (.bin .add (.reg 14)
           (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 7)) (.bin .mul (.reg 7) (.reg 5)))
             (.bin .mul (.const 2) (.reg 5)))) ;;
         .assign 16 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
         .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 16) ;;
         .assign 17 (.const 0))
        { mem := c.mem0, regs := regs1, pos := pos_s } o st' c0 ∧
        normalPost (fun st =>
          st.mem = Function.update c.mem0 (c.b + dsGenOff) (c.mem0 (c.b + dsGenOff) + 1) ∧
          st.regs 0 = c.b ∧ st.regs 1 = c.stepHdrsPtr ∧ st.regs 2 = c.m ∧ st.regs 3 = c.dOutPtr ∧
          st.regs 11 = dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap ∧
          st.regs 15 = dsEStampBase c.b c.L c.vCap c.eCap ∧
          st.regs 16 = c.mem0 (c.b + dsGenOff) + 1 ∧ st.regs 17 = 0 ∧
          st.regs 27 = (if c.isReemb then 5 else 3) ∧
          st.regs 28 = (if c.isReemb then 6 else 4)) o st' ∧
        k0 + c0 ≤ 210 := by
    intro k0 regs1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 hk0
    have htail : ∀ (k1 : ℕ) (regs2 : ℕ → ℕ),
        regs2 0 = c.b → regs2 1 = c.stepHdrsPtr → regs2 2 = c.m → regs2 3 = c.dOutPtr →
        regs2 5 = c.vCap → regs2 6 = c.eCap → regs2 7 = c.L + 1 →
        regs2 8 = dynGraphSize c.vCap c.eCap → regs2 10 = dsHPtr c.b c.vCap c.eCap →
        regs2 11 = dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap →
        regs2 27 = (if c.isReemb then 5 else 3) →
        regs2 28 = (if c.isReemb then 6 else 4) →
        k1 + 140 ≤ 210 →
        ∃ o st' c0, Runs c.w p ω
          (.assign 12 (.bin .add (.bin .add (.reg 10) (.reg 8)) (.reg 8)) ;;
           .assign 13 (.bin .add (.reg 12)
             (.bin .add (.bin .mul (.const 3) (.reg 6)) (.bin .mul (.const 2) (.reg 7)))) ;;
           .assign 14 (.bin .add (.reg 13)
             (.bin .add (.reg 7)
               (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 7) (.reg 6)))
                 (.bin .mul (.const 2) (.bin .mul (.reg 7) (.reg 5)))))) ;;
           .assign 15 (.bin .add (.reg 14)
             (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 7)) (.bin .mul (.reg 7) (.reg 5)))
               (.bin .mul (.const 2) (.reg 5)))) ;;
           .assign 16 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
           .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 16) ;;
           .assign 17 (.const 0))
          { mem := c.mem0, regs := regs2, pos := pos_s } o st' c0 ∧
          normalPost (fun st =>
            st.mem = Function.update c.mem0 (c.b + dsGenOff) (c.mem0 (c.b + dsGenOff) + 1) ∧
            st.regs 0 = c.b ∧ st.regs 1 = c.stepHdrsPtr ∧ st.regs 2 = c.m ∧ st.regs 3 = c.dOutPtr ∧
            st.regs 11 = dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap ∧
            st.regs 15 = dsEStampBase c.b c.L c.vCap c.eCap ∧
            st.regs 16 = c.mem0 (c.b + dsGenOff) + 1 ∧ st.regs 17 = 0 ∧
            st.regs 27 = (if c.isReemb then 5 else 3) ∧
            st.regs 28 = (if c.isReemb then 6 else 4)) o st' ∧
          k1 + c0 ≤ 210 := by
      intro k1 regs2 t0 t1 t2 t3 t5 t6 t7 t8 t10 t11 t27 t28 hk1
      refine runs_seq_assign_le (v := dsMinHBase c.b c.vCap c.eCap)
        (emin ▸ Expr.eval_add
          (eaux ▸ Expr.eval_add (Expr.eval_reg_of_eq t10) (Expr.eval_reg_of_eq t8) (eaux.symm ▸ hauxW))
          (Expr.eval_reg_of_eq t8) (emin.symm ▸ hminW)) ?_
      refine runs_seq_assign_le (v := dsDomGenBase c.b c.L c.vCap c.eCap)
        (edom ▸ Expr.eval_add (Expr.eval_reg_of_eq (v := dsMinHBase c.b c.vCap c.eCap) (by simp))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := c.eCap) (by simp [t6])) h3e)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := c.L + 1) (by simp [t7])) h2L1)
            h3e2L1)
          (edom.symm ▸ hdomW)) ?_
      refine runs_seq_assign_le (v := dsSGenBase c.b c.L c.vCap c.eCap)
        (esGen ▸ Expr.eval_add (Expr.eval_reg_of_eq (v := dsDomGenBase c.b c.L c.vCap c.eCap) (by simp))
          (Expr.eval_add (Expr.eval_reg_of_eq (v := c.L + 1) (by simp [t7]))
            (Expr.eval_add
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_mul (Expr.eval_reg_of_eq (v := c.L + 1) (by simp [t7]))
                  (Expr.eval_reg_of_eq (v := c.eCap) (by simp [t6])) hLe) h2Le)
              (Expr.eval_mul (Expr.eval_const (by omega))
                (Expr.eval_mul (Expr.eval_reg_of_eq (v := c.L + 1) (by simp [t7]))
                  (Expr.eval_reg_of_eq (v := c.vCap) (by simp [t5])) hLv) h2Lv)
              h2Le2Lv)
            hdomOff)
          (esGen.symm ▸ hsGenW)) ?_
      refine runs_seq_assign_le (v := dsEStampBase c.b c.L c.vCap c.eCap)
        (eeSt ▸ Expr.eval_add (Expr.eval_reg_of_eq (v := dsSGenBase c.b c.L c.vCap c.eCap) (by simp))
          (Expr.eval_add
            (Expr.eval_add
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := c.L + 1) (by simp [t7])) h2L1)
              (Expr.eval_mul (Expr.eval_reg_of_eq (v := c.L + 1) (by simp [t7]))
                (Expr.eval_reg_of_eq (v := c.vCap) (by simp [t5])) hLv)
              h2L1Lv)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := c.vCap) (by simp [t5])) h2v)
            hsOff)
          (eeSt.symm ▸ heStW)) ?_
      refine runs_seq_assign_le (v := c.mem0 (c.b + dsGenOff) + 1)
        (Expr.eval_add
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := c.b) (by simp [t0]))
            (Expr.eval_const (by simp [dsGenOff]; omega)) hbG) rfl)
          (Expr.eval_const (by omega)) c.hgen_w) ?_
      refine runs_seq_store_le (x := c.b + dsGenOff) (v := c.mem0 (c.b + dsGenOff) + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := c.b) (by simp [t0]))
          (Expr.eval_const (by simp [dsGenOff]; omega)) hbG)
        (Expr.eval_reg_of_eq (v := c.mem0 (c.b + dsGenOff) + 1) (by simp)) ?_
      refine runs_assign_le (v := 0) (Expr.eval_const (by omega))
        ⟨rfl, by simp [t0], by simp [t1], by simp [t2], by simp [t3], by simp [t11], by simp, by simp,
          by simp, by simp [t27], by simp [t28]⟩ ?_
      simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load]; omega
    refine runs_seq_cond_le (v := if c.isReemb then 1 else 0) (Expr.eval_reg_of_eq s4)
      (fun hne => ?_) (fun h0 => ?_)
    · have htr : c.isReemb = true := by cases hc : c.isReemb <;> simp [hc] at hne ⊢
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := dgEPresBase (dsGPtr c.b) c.vCap)
        (egPres ▸ Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := c.mem0, regs := regs1, pos := pos_s }) s9)
            (Expr.eval_const (by omega)) hgP4W)
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (st := { mem := c.mem0, regs := regs1, pos := pos_s }) s5) h7v)
          (egPres.symm ▸ hgPresW)) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := 5) (Expr.eval_const (by omega)) ?_
      refine runs_seq_assign_le (v := 6) (Expr.eval_const (by omega)) ?_
      exact htail _ _ (by simp [s0]) (by simp [s1]) (by simp [s2]) (by simp [s3])
        (by simp [s5]) (by simp [s6]) (by simp [s7]) (by simp [s8]) (by simp [s10])
        (by simp [htr]) (by simp [htr]) (by simp [htr])
        (by simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega)
    · have hfl : c.isReemb = false := by cases hc : c.isReemb <;> simp [hc] at h0 ⊢
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := dgEPresBase (dsHPtr c.b c.vCap c.eCap) c.vCap)
        (ehPres ▸ Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (st := { mem := c.mem0, regs := regs1, pos := pos_s }) s10)
            (Expr.eval_const (by omega)) hhP4W)
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (st := { mem := c.mem0, regs := regs1, pos := pos_s }) s5) h7v)
          (ehPres.symm ▸ hhPresW)) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := 3) (Expr.eval_const (by omega)) ?_
      refine runs_seq_assign_le (v := 4) (Expr.eval_const (by omega)) ?_
      exact htail _ _ (by simp [s0]) (by simp [s1]) (by simp [s2]) (by simp [s3])
        (by simp [s5]) (by simp [s6]) (by simp [s7]) (by simp [s8]) (by simp [s10])
        (by simp [hfl]) (by simp [hfl]) (by simp [hfl])
        (by simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega)
  exact hcond _ _ (by simp [r0]) (by simp [r1]) (by simp [r2]) (by simp [r3]) (by simp [r4])
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load]; omega)

/-! ## Inner loop scanning one step's `D`-list -/

private def CollectDInnerInv (c : CollectDCtx) (baseOut : List ℕ) (dPtr : ℕ) (dL : List ℕ)
    (outerIdx : ℕ) (j : ℕ) (st : State) : Prop :=
  let gD := c.mem0 (c.b + dsGenOff) + 1
  let hPres := dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap
  let eStamp := dsEStampBase c.b c.L c.vCap c.eCap
  ∃ dOut : List ℕ,
    st.regs 0 = c.b ∧ st.regs 1 = c.stepHdrsPtr ∧ st.regs 2 = c.m ∧ st.regs 3 = c.dOutPtr ∧
    st.regs 11 = hPres ∧ st.regs 15 = eStamp ∧ st.regs 16 = gD ∧ st.regs 17 = dOut.length ∧
    st.regs 18 = outerIdx ∧ st.regs 20 = dPtr ∧ st.regs 21 = dL.length ∧ st.regs 22 = j ∧
    st.regs 27 = (if c.isReemb then 5 else 3) ∧ st.regs 28 = (if c.isReemb then 6 else 4) ∧
    dOut.length ≤ baseOut.length + j ∧
    dOut.Nodup ∧
    (∀ e, e ∈ dOut ↔ e ∈ baseOut ∨ (e ∈ dL.take j ∧ e ∈ c.H.E)) ∧
    ListAt st.mem c.dOutPtr dOut ∧
    st.mem (c.b + dsGenOff) = gD ∧
    (∀ e < c.eCap, st.mem (eStamp + e) ≤ gD ∧ (st.mem (eStamp + e) = gD ↔ e ∈ dOut)) ∧
    ∀ a, a ≠ c.b + dsGenOff → (a < eStamp ∨ eStamp + c.eCap ≤ a) →
      (a < c.dOutPtr ∨ c.dOutPtr + dOut.length ≤ a) → st.mem a = c.mem0 a

private def collectDInnerBody : Stmt :=
  .assign 23 (.load (.bin .add (.reg 20) (.reg 22))) ;;
  .assign 24 (.load (.bin .add (.reg 11) (.reg 23))) ;;
  .cond (.reg 24)
    (.assign 25 (.load (.bin .add (.reg 15) (.reg 23))) ;;
     .cond (.bin .eq (.reg 25) (.reg 16))
       .nop
       (.store (.bin .add (.reg 15) (.reg 23)) (.reg 16) ;;
        .store (.bin .add (.reg 3) (.reg 17)) (.reg 23) ;;
        .assign 17 (.bin .add (.reg 17) (.const 1))))
    .nop

private lemma collectD_inner_triple (c : CollectDCtx) {p : Program}
    {baseOut dL : List ℕ} {dPtr outerIdx : ℕ}
    (hbase_le : baseOut.length + dL.length ≤ ∑ r : Fin c.m, (c.dLists r).length)
    (hdPtr_fix : c.b + dsFixedSize c.L c.vCap c.eCap ≤ dPtr)
    (hdPtr_out : dPtr + dL.length ≤ c.dOutPtr)
    (hdL_at : ListAt c.mem0 dPtr dL)
    (hdL_cap : ∀ e ∈ dL, e < c.eCap) :
    Triple c.w p
      (fun st => CollectDInnerInv c baseOut dPtr dL outerIdx 0
        { st with regs := Function.update st.regs 22 0 })
      (forRange 22 (.const 0) (.reg 21) collectDInnerBody)
      (normalPost (CollectDInnerInv c baseOut dPtr dL outerIdx dL.length))
      (fun _ => 58 * dL.length + 12) := by
  have h16 := c.hw16
  have hfw := c.hfix_w
  have hdL_w : dL.length < 2 ^ c.w := by have := c.hdOut_w; omega
  obtain ⟨hgo, _, hG_e, hH_e, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hek, hks_top⟩ :=
    collectD_lt_eStamp_bounds c.b c.L c.vCap c.eCap
  have hhPres_lt_est :
      dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap + c.eCap ≤
      dsEStampBase c.b c.L c.vCap c.eCap := by
    cases c.isReemb <;> simp only [Bool.false_eq_true, ↓reduceIte, dgEPresBase, dynGraphSize] at hG_e hH_e ⊢ <;> omega
  have heSt_top : dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤
      c.b + dsFixedSize c.L c.vCap c.eCap := hek.symm ▸ ((Nat.le_add_right _ _).trans hks_top)
  have hbGen_lt_hPres : c.b + dsGenOff <
      dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap := by
    have : dsGPtr c.b ≤ dsHPtr c.b c.vCap c.eCap := Nat.le_add_right _ _
    cases c.isReemb <;> simp only [Bool.false_eq_true, ↓reduceIte, dgEPresBase] <;> omega
  refine (Triple.forRange_const 45 0 dL.length (Nat.zero_le _) (by omega) (fun _ => hdL_w)
    (Inv := CollectDInnerInv c baseOut dPtr dL outerIdx)
    (fun _ h => ⟨Expr.eval_const (by omega), h⟩)
    (fun _ _ _ _ h => by rcases h with ⟨_, h⟩; exact h.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => by rcases h with ⟨_, h⟩; exact Expr.eval_reg_of_eq h.2.2.2.2.2.2.2.2.2.2.1)
    (fun j _ hj => ?_)).conseq (fun _ h => h) (fun _ _ h => h)
    (fun _ _ => by simp [Expr.size]; omega)
  intro st ω ⟨dOut, r0, r1, r2, r3, r11, r15, r16, r17, r18, r20, r21, r22, r27, r28,
    hlen_le, hnd, hmemD, hAt, hgen, heSt, hFr⟩
  set gD := c.mem0 (c.b + dsGenOff) + 1
  set hPres := dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap
  set eStamp := dsEStampBase c.b c.L c.vCap c.eCap
  set e := dL[j]'hj
  have he_cap : e < c.eCap := hdL_cap e (List.getElem_mem hj)
  have htake : dL.take (j + 1) = dL.take j ++ [e] := List.take_succ_eq_append_getElem hj
  have hd_mem : st.mem (dPtr + j) = e := by
    rw [hFr (dPtr + j) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hdL_at j hj
  have hh_mem : st.mem (hPres + e) = c.mem0 (hPres + e) :=
    hFr (hPres + e) (by omega) (Or.inl (by omega)) (Or.inl (by have := c.hfix_out; omega))
  have hhPres_lt : hPres + e < 2 ^ c.w := by omega
  have heSt_lt : eStamp + e < 2 ^ c.w := by omega
  have hdPtr_lt : dPtr + j < 2 ^ c.w := by have := c.hdOut_w; omega
  have hdOut_lt : c.dOutPtr + dOut.length < 2 ^ c.w := by have := c.hdOut_w; omega
  have hdOut_len1_lt : dOut.length + 1 < 2 ^ c.w := by have := c.hdOut_w; omega
  dsimp only [collectDInnerBody]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r20) (Expr.eval_reg_of_eq r22)
      hdPtr_lt) hd_mem) ?_
  refine runs_seq_assign_le (v := c.mem0 (hPres + e))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := hPres) (by simp [r11]))
      (Expr.eval_reg_of_eq (v := e) (by simp)) hhPres_lt) hh_mem) ?_
  refine runs_cond_le (Expr.eval_reg_of_eq (v := c.mem0 (hPres + e)) (by simp))
    (fun hinH => ?_) (fun hnotH => ?_)
  · have heH : e ∈ c.H.E := (c.hH e he_cap).mp hinH
    refine runs_seq_assign_le (v := st.mem (eStamp + e))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := eStamp) (by simp [r15]))
        (Expr.eval_reg_of_eq (v := e) (by simp)) heSt_lt) rfl) ?_
    by_cases hseen : st.mem (eStamp + e) = gD
    · have heD : e ∈ dOut := (heSt e he_cap).2.mp hseen
      refine runs_cond_le
        (Expr.eval_eq_true (Expr.eval_reg_of_eq (v := st.mem (eStamp + e)) (by simp))
          (Expr.eval_reg_of_eq (v := gD) (by simp [r16])) hseen (by omega))
        (fun _ => ?_) (fun h => by omega)
      refine runs_nop_le ?_ (by simp only [Expr.size_reg, Expr.size_bin, Expr.size_load]; omega)
      refine ⟨⟨dOut, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r11, hPres],
        by simp [r15, eStamp], by simp [r16, gD], by simp [r17], by simp [r18], by simp [r20], by simp [r21],
        by simp, by simp [r27], by simp [r28], by omega, hnd, fun x => ?_, hAt, hgen, heSt, hFr⟩, by simp [r22]⟩
      rw [hmemD x, htake]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl h1, h2⟩
      · rintro (h | ⟨h1 | rfl, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2⟩
        · exact (hmemD e).mp heD
    · have heNotD : e ∉ dOut := fun h => hseen ((heSt e he_cap).2.mpr h)
      refine runs_cond_le
        (Expr.eval_eq_false (Expr.eval_reg_of_eq (v := st.mem (eStamp + e)) (by simp))
          (Expr.eval_reg_of_eq (v := gD) (by simp [r16])) hseen (by omega))
        (fun h => by omega) (fun _ => ?_)
      refine runs_seq_store_le (x := eStamp + e) (v := gD)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := eStamp) (by simp [r15]))
          (Expr.eval_reg_of_eq (v := e) (by simp)) heSt_lt)
        (Expr.eval_reg_of_eq (v := gD) (by simp [r16])) ?_
      refine runs_seq_store_le (x := c.dOutPtr + dOut.length) (v := e)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := c.dOutPtr) (by simp [r3]))
          (Expr.eval_reg_of_eq (v := dOut.length) (by simp [r17])) hdOut_lt)
        (Expr.eval_reg_of_eq (v := e) (by simp)) ?_
      refine runs_assign_le (v := dOut.length + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dOut.length) (by simp [r17]))
          (Expr.eval_const (by omega)) hdOut_len1_lt) ?_ ?_
      · set mem' := Function.update (Function.update st.mem (eStamp + e) gD)
          (c.dOutPtr + dOut.length) e
        refine ⟨⟨dOut ++ [e], by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r11, hPres],
          by simp [r15, eStamp], by simp [r16, gD], by simp, by simp [r18], by simp [r20], by simp [r21],
          by simp, by simp [r27], by simp [r28], by simp; omega, List.nodup_append.mpr ⟨hnd, List.nodup_singleton e,
            fun x hx y hy hxy => heNotD (by rw [List.mem_singleton.mp hy] at hxy; rwa [← hxy])⟩,
          fun x => ?_, ?_, ?_, ?_, ?_⟩, by simp [r22]⟩
        · rw [List.mem_append, List.mem_singleton, hmemD x, htake]
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro ((h | ⟨h1, h2⟩) | rfl)
            · exact Or.inl h
            · exact Or.inr ⟨Or.inl h1, h2⟩
            · exact Or.inr ⟨Or.inr rfl, heH⟩
          · rintro (h | ⟨h1 | rfl, h2⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr ⟨h1, h2⟩)
            · exact Or.inr rfl
        · intro idx hidx
          dsimp only [mem']
          by_cases hlast : idx = dOut.length
          · subst hlast
            simp [Function.update]
          · have hlt_d : idx < dOut.length := by simp at hidx; omega
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by have := c.hfix_out; omega),
              List.getElem_append_left hlt_d]
            exact hAt idx hlt_d
        · dsimp only [mem']
          rw [Function.update_of_ne (by have := c.hfix_out; omega),
            Function.update_of_ne (by omega)]
          exact hgen
        · intro e' he'
          dsimp only [mem']
          rw [Function.update_of_ne (by have := c.hfix_out; omega)]
          by_cases heq : e' = e
          · subst heq; simp [Function.update, eStamp, gD]
          · rw [Function.update_of_ne (by omega)]
            have := heSt e' he'
            refine ⟨this.1, ?_⟩
            rw [this.2, List.mem_append, List.mem_singleton]
            exact ⟨Or.inl, fun h => h.elim id fun h' => (heq h').elim⟩
        · intro a ha1 ha2 ha3
          dsimp only [mem']
          rw [Function.update_of_ne (by simp at ha3; omega),
            Function.update_of_ne (by omega)]
          exact hFr a ha1 ha2 (by simp at ha3; omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load]; omega
  · have heNotH : e ∉ c.H.E := fun h => ((c.hH e he_cap).mpr h) hnotH
    refine runs_nop_le ?_ (by simp only [Expr.size_reg, Expr.size_bin, Expr.size_load]; omega)
    refine ⟨⟨dOut, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r11, hPres],
      by simp [r15, eStamp], by simp [r16, gD], by simp [r17], by simp [r18], by simp [r20], by simp [r21],
      by simp, by simp [r27], by simp [r28], by omega, hnd, fun x => ?_, hAt, hgen, heSt, hFr⟩, by simp [r22]⟩
    rw [hmemD x, htake]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl h1, h2⟩
    · rintro (h | ⟨h1 | rfl, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
      · exact (heNotH h2).elim

/-! ## Outer loop and main contract -/

private def CollectDOuterInv (c : CollectDCtx) (i : ℕ) (st : State) : Prop :=
  let gD := c.mem0 (c.b + dsGenOff) + 1
  let hPres := dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap
  let eStamp := dsEStampBase c.b c.L c.vCap c.eCap
  ∃ dOut : List ℕ,
    st.regs 0 = c.b ∧ st.regs 1 = c.stepHdrsPtr ∧ st.regs 2 = c.m ∧ st.regs 3 = c.dOutPtr ∧
    st.regs 11 = hPres ∧ st.regs 15 = eStamp ∧ st.regs 16 = gD ∧ st.regs 17 = dOut.length ∧
    st.regs 18 = i ∧
    st.regs 27 = (if c.isReemb then 5 else 3) ∧ st.regs 28 = (if c.isReemb then 6 else 4) ∧
    dOut.length ≤ (((List.finRange c.m).take i).map fun r => (c.dLists r).length).sum ∧
    dOut.Nodup ∧
    (∀ e, e ∈ dOut ↔ (∃ r : Fin c.m, r.1 < i ∧ e ∈ c.dLists r) ∧ e ∈ c.H.E) ∧
    ListAt st.mem c.dOutPtr dOut ∧
    st.mem (c.b + dsGenOff) = gD ∧
    (∀ e < c.eCap, st.mem (eStamp + e) ≤ gD ∧ (st.mem (eStamp + e) = gD ↔ e ∈ dOut)) ∧
    ∀ a, a ≠ c.b + dsGenOff → (a < eStamp ∨ eStamp + c.eCap ≤ a) →
      (a < c.dOutPtr ∨ c.dOutPtr + dOut.length ≤ a) → st.mem a = c.mem0 a

public section

/-- `dsCollectBatchDStmt` meets `dsCollectBatchDContract`. -/
theorem dsCollectBatchD_meetsContract (c : CollectDCtx) {p : Program}
    {bAux bPhase bSZ bPosFull bUL : ℕ}
    (hpUL : p.HasAt bUL (updateLoopProcs bAux bPhase bSZ bPosFull bUL)) :
    MeetsContract c.w p (bUL + updateLoopIdxCollectD) (dsCollectBatchDContract c) := by
  refine meetsContract_of_runs
    (hpUL.get (i := updateLoopIdxCollectD) (by simp [updateLoopProcs, updateLoopIdxCollectD])) ?_
  rintro args mem0 pos ω _ ⟨rfl, rfl⟩
  have h16 := c.hw16
  have hfw := c.hfix_w
  obtain ⟨hgo, _, hG_e, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hek, hks_top⟩ :=
    collectD_lt_eStamp_bounds c.b c.L c.vCap c.eCap
  have heSt_top : dsEStampBase c.b c.L c.vCap c.eCap + c.eCap ≤
      c.b + dsFixedSize c.L c.vCap c.eCap := hek.symm ▸ ((Nat.le_add_right _ _).trans hks_top)
  have hbGen_lt_eSt : c.b + dsGenOff < dsEStampBase c.b c.L c.vCap c.eCap :=
    lt_of_lt_of_le hgo ((Nat.le_add_right _ _).trans hG_e)
  set outerBody : Stmt :=
    .assign 19 (.load (.bin .add (.reg 1) (.reg 18))) ;;
    .assign 20 (.load (.bin .add (.reg 19) (.reg 27))) ;;
    .assign 21 (.load (.bin .add (.reg 19) (.reg 28))) ;;
    forRange 22 (.const 0) (.reg 21) collectDInnerBody
  set stepCost : ℕ → ℕ := fun i =>
    if hi : i < c.m then 58 * (c.dLists ⟨i, hi⟩).length + 40 else 40
  have houter : Triple c.w p
      (fun st =>
        st.mem = Function.update c.mem0 (c.b + dsGenOff) (c.mem0 (c.b + dsGenOff) + 1) ∧
        st.regs 0 = c.b ∧ st.regs 1 = c.stepHdrsPtr ∧ st.regs 2 = c.m ∧ st.regs 3 = c.dOutPtr ∧
        st.regs 11 = dgEPresBase (if c.isReemb then dsGPtr c.b else dsHPtr c.b c.vCap c.eCap) c.vCap ∧
        st.regs 15 = dsEStampBase c.b c.L c.vCap c.eCap ∧
        st.regs 16 = c.mem0 (c.b + dsGenOff) + 1 ∧ st.regs 17 = 0 ∧
        st.regs 27 = (if c.isReemb then 5 else 3) ∧
        st.regs 28 = (if c.isReemb then 6 else 4))
      (forRange 18 (.const 0) (.reg 2) outerBody)
      (normalPost (CollectDOuterInv c c.m))
      (fun _ => rangeCost stepCost 0 c.m + c.m * 9 + 7) := by
    refine (Triple.forRange_le stepCost 0 c.m (Nat.zero_le _) (by omega)
      (fun _ => by have := c.hhdrs_w; omega) (Inv := CollectDOuterInv c)
      (fun st ⟨hm, r0, r1, r2, r3, r11, r15, r16, r17, r27, r28⟩ => ⟨Expr.eval_const (by omega), by
        refine ⟨[], by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r11],
          by simp [r15], by simp [r16], by simp [r17], by simp, by simp [r27], by simp [r28],
          by simp, List.nodup_nil,
          by simp, by intro i hi; simp at hi, by simp [hm, Function.update], fun e he => ?_,
          fun a ha1 _ _ => by simp [hm, Function.update_of_ne ha1]⟩
        have hlt_g := c.hES e he
        rw [hm, Function.update_of_ne (by omega)]
        exact ⟨by omega, by constructor <;> intro h <;> [omega; cases h]⟩⟩)
      (fun _ _ _ _ h => by rcases h with ⟨_, h⟩; exact h.2.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ h => by rcases h with ⟨_, h⟩; exact Expr.eval_reg_of_eq h.2.2.1)
      (fun i _ hi => ?_)).conseq (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp [Expr.size])
    intro st ω' ⟨dOut, r0, r1, r2, r3, r11, r15, r16, r17, r18, r27, r28, hlen_le, hnd, hmemD,
      hAt, hgen, heSt, hFr⟩
    have hstep := c.hSteps ⟨i, hi⟩
    dsimp only at hstep
    obtain ⟨hh_fix, hh_out, hdP_fix, hdP_out, hdL_eq, hdL_at, hdL_cap⟩ := hstep
    set h_i := c.mem0 (c.stepHdrsPtr + i)
    set ptrOff := if c.isReemb then 5 else 3
    set lenOff := if c.isReemb then 6 else 4
    have hptrOff_lt : ptrOff < 7 := by dsimp only [ptrOff]; split_ifs <;> omega
    have hlenOff_lt : lenOff < 7 := by dsimp only [lenOff]; split_ifs <;> omega
    set dPtr_i := c.mem0 (h_i + ptrOff)
    set dLen_i := c.mem0 (h_i + lenOff)
    have hhdr_mem : st.mem (c.stepHdrsPtr + i) = h_i :=
      hFr _ (by have := c.hfix_hdrs; omega) (Or.inr (by have := c.hfix_hdrs; omega))
        (Or.inl (by have := c.hhdrs_out; omega))
    have hdP_mem : st.mem (h_i + ptrOff) = dPtr_i :=
      hFr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))
    have hdL_mem : st.mem (h_i + lenOff) = dLen_i :=
      hFr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))
    have hbase_le : dOut.length + (c.dLists ⟨i, hi⟩).length ≤ ∑ r : Fin c.m, (c.dLists r).length := by
      have h1 : (((List.finRange c.m).take i).map fun r => (c.dLists r).length).sum +
          (c.dLists ⟨i, hi⟩).length =
          (((List.finRange c.m).take (i + 1)).map fun r => (c.dLists r).length).sum :=
        (sum_finRange_take_succ hi fun r => (c.dLists r).length).symm
      exact le_trans (Nat.add_le_add_right hlen_le _)
        (h1 ▸ sum_finRange_take_le fun r => (c.dLists r).length)
    have hstep_eq : stepCost i = 58 * (c.dLists ⟨i, hi⟩).length + 40 := by simp [stepCost, hi]
    dsimp only [outerBody]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := h_i)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r18)
        (by have := c.hhdrs_w; omega)) hhdr_mem) ?_
    refine runs_seq_assign_le (v := dPtr_i)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h_i) (by simp))
        (Expr.eval_reg_of_eq (v := ptrOff) (by simp [r27, ptrOff])) (by have := c.hdOut_w; omega)) hdP_mem) ?_
    refine runs_seq_assign_le (v := dLen_i)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h_i) (by simp))
        (Expr.eval_reg_of_eq (v := lenOff) (by simp [r28, lenOff])) (by have := c.hdOut_w; omega)) hdL_mem) ?_
    refine runs_triple_le (collectD_inner_triple c (outerIdx := i) hbase_le hdP_fix
        (hdL_eq ▸ hdP_out) hdL_at hdL_cap)
      ⟨dOut, by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r11], by simp [r15],
        by simp [r16], by simp [r17], by simp [r18], by simp, by simp [hdL_eq], by simp,
        by simp [r27, ptrOff], by simp [r28, lenOff],
        by omega, hnd, fun e => by simp [hmemD], hAt, hgen, heSt, hFr⟩
      (fun o st1 hpost => ?_) ?_
    · rcases o with _ | _
      · rcases hpost with ⟨dOut', s0, s1, s2, s3, s11, s15, s16, s17, s18, _, _, _, s27, s28,
          hlen', hnd', hmem', hAt', hgen', heSt', hFr'⟩
        refine ⟨⟨dOut', by simp [s0], by simp [s1], by simp [s2], by simp [s3], by simp [s11],
          by simp [s15], by simp [s16], by simp [s17], by simp, by simp [s27], by simp [s28],
          ?_, hnd', fun e => ?_,
          hAt', hgen', heSt', hFr'⟩, s18⟩
        · rw [sum_finRange_take_succ hi]; omega
        · rw [hmem' e, List.take_length, hmemD e]
          constructor
          · rintro (⟨⟨r, hr, hre⟩, heH⟩ | ⟨heL, heH⟩)
            · exact ⟨⟨r, Nat.lt_succ_of_lt hr, hre⟩, heH⟩
            · exact ⟨⟨⟨i, hi⟩, Nat.lt_succ_self i, heL⟩, heH⟩
          · rintro ⟨⟨r, hr, hre⟩, heH⟩
            by_cases hri : r.1 = i
            · have hr_eq : r = ⟨i, hi⟩ := Fin.ext hri
              exact Or.inr ⟨hr_eq ▸ hre, heH⟩
            · exact Or.inl ⟨⟨r, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hr) hri, hre⟩, heH⟩
      · exact hpost.elim
    · rw [hstep_eq]; simp only [Expr.size_reg, Expr.size_bin, Expr.size_load]; omega
  simp only [updateLoopProcs, updateLoopIdxCollectD, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsCollectBatchDStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le (collectD_setup_triple c)
    ⟨rfl, by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [startState]⟩ ?_
  rintro st1 h1
  refine runs_seq_triple_le houter h1 ?_
  rintro st2 ⟨dOut, _, _, _, _, _, _, _, s17, _, _, _, hlen_le, hnd, hmemD, hAt, hgen, heSt, hFr⟩
  refine runs_ret_le (v := dOut.length) (Expr.eval_reg_of_eq s17) ?_ ?_
  · have hlen_sum : dOut.length ≤ ∑ r : Fin c.m, (c.dLists r).length := by
      simpa [List.take_of_length_le (show (List.finRange c.m).length ≤ c.m by simp),
        sum_finRange_eq_finset_sum] using hlen_le
    refine ⟨dOut, rfl, hlen_sum, hnd, fun e => ?_, hAt, hgen,
      fun e he => hgen ▸ (heSt e he).1, hFr⟩
    rw [hmemD e]
    simp only [Fin.is_lt, true_and]
  · have hrc : rangeCost stepCost 0 c.m =
        ∑ r ∈ Finset.range c.m, (58 * (if hr : r < c.m then (c.dLists ⟨r, hr⟩).length else 0) + 40) := by
      rw [rangeCost_eq_sum_range stepCost c.m 0 c.m (by omega)]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hrm : r < c.m := Finset.mem_range.mp hr
      simp [stepCost, hrm]
    have hsum_fin : (∑ r ∈ Finset.range c.m,
        if hr : r < c.m then (c.dLists ⟨r, hr⟩).length else 0) =
        ∑ i : Fin c.m, (c.dLists i).length := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => if hr : r < c.m then (c.dLists ⟨r, hr⟩).length else 0)]
      refine Finset.sum_congr rfl fun i _ => by simp
    have hrc_eq : rangeCost stepCost 0 c.m = 58 * (∑ i : Fin c.m, (c.dLists i).length) + 40 * c.m := by
      rw [hrc, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_fin, Finset.sum_const,
        Finset.card_range, smul_eq_mul]; ring
    dsimp only [dsCollectBatchDContract, Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
