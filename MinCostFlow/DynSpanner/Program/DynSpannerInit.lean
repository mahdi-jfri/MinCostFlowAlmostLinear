module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitAt

import Mathlib.Tactic.Ring

/-!
# Verification of `dsInitStmt` (`DynSpannerInit`)

Verifies `dsInit_meetsContract` for `initProcs` at `initIdx`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private lemma dsInit_offset_cont {w L vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w) (hfix_w : dsFixedSize L vCap eCap < 2 ^ w)
    (hr0 : st.regs 0 = L) (hr2 : st.regs 2 = vCap) (hr3 : st.regs 3 = eCap)
    (hrest : ∀ st₁ : State,
      st₁.mem = st.mem ∧ (∀ r ≤ 8, st₁.regs r = st.regs r) ∧
      st₁.regs 9 = dynGraphSize vCap eCap ∧ st₁.regs 10 = dsFixedSize L vCap eCap →
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ (k + 75) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 9 (.bin .add (.const 4)
        (.bin .add (.bin .mul (.const 7) (.reg 2)) (.bin .mul (.const 9) (.reg 3)))) ;;
       .assign 10 (.bin .add
         (.bin .add (.const dsHdrSize) (.bin .mul (.const 3) (.reg 9)))
         (.bin .add (.bin .mul (.const 3) (.reg 3))
           (.bin .mul (.const 2) (.bin .add (.reg 0) (.const 1))))) ;;
       .assign 10 (.bin .add (.reg 10)
         (.bin .add (.bin .add (.reg 0) (.const 1))
           (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 0) (.const 1)) (.reg 3))))) ;;
       .assign 10 (.bin .add (.reg 10)
         (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 0) (.const 1)) (.reg 2)))
           (.bin .add (.bin .mul (.const 2) (.bin .add (.reg 0) (.const 1))) (.reg 2)))) ;;
       .assign 10 (.bin .add (.reg 10)
         (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 3)))) ;; s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  have hm := dsMEmbTempBase_eq 0 L vCap eCap
  have hrev := dsRevGenBase_eq 0 L vCap eCap
  have hdg := dsDomGenBase_eq 0 L vCap eCap
  have hmn := dsMinHBase_eq 0 vCap eCap
  have hfx := dsFixedSize_add 0 L vCap eCap
  simp only [Nat.zero_add] at hm hrev hdg hmn hfx
  have h_dg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have h_hdr : dsHdrSize = 6 := rfl
  set s0 := dsHdrSize + 3 * dynGraphSize vCap eCap + (3 * eCap + 2 * (L + 1))
  set s1 := s0 + ((L + 1) + 2 * ((L + 1) * eCap))
  set s2 := s1 + (3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap))
  set s3 := s2 + (vCap + 3 * eCap)
  have hs3_eq : s3 = dsFixedSize L vCap eCap := by
    dsimp only [s3, s2, s1, s0]; omega
  have hs3_w : s3 < 2 ^ w := hs3_eq ▸ hfix_w
  have hs0_w : s0 < 2 ^ w := by dsimp only [s3, s2, s1] at hs3_w; omega
  have hs1_w : s1 < 2 ^ w := by dsimp only [s3, s2] at hs3_w; omega
  have hs2_w : s2 < 2 ^ w := by dsimp only [s3] at hs3_w; omega
  have hdg_w : dynGraphSize vCap eCap < 2 ^ w := by dsimp only [s0] at hs0_w; omega
  have h7v : 7 * vCap < 2 ^ w := by dsimp only [dynGraphSize] at hdg_w; omega
  have h9e : 9 * eCap < 2 ^ w := by dsimp only [dynGraphSize] at hdg_w; omega
  have h79 : 7 * vCap + 9 * eCap < 2 ^ w := by dsimp only [dynGraphSize] at hdg_w; omega
  have hL1 : L + 1 < 2 ^ w := by dsimp only [s0] at hs0_w; omega
  have h2L1 : 2 * (L + 1) < 2 ^ w := by dsimp only [s0] at hs0_w; omega
  have h3dg : 3 * dynGraphSize vCap eCap < 2 ^ w := by dsimp only [s0] at hs0_w; omega
  have h6_3dg : dsHdrSize + 3 * dynGraphSize vCap eCap < 2 ^ w := by dsimp only [s0] at hs0_w; omega
  have h3e : 3 * eCap < 2 ^ w := by dsimp only [s0] at hs0_w; omega
  have h3e_2L1 : 3 * eCap + 2 * (L + 1) < 2 ^ w := by dsimp only [s0] at hs0_w; omega
  have hLe : (L + 1) * eCap < 2 ^ w := by dsimp only [s1] at hs1_w; omega
  have h2Le : 2 * ((L + 1) * eCap) < 2 ^ w := by dsimp only [s1] at hs1_w; omega
  have hs1_diff : (L + 1) + 2 * ((L + 1) * eCap) < 2 ^ w := by dsimp only [s1] at hs1_w; omega
  have hLv : (L + 1) * vCap < 2 ^ w := by dsimp only [s2] at hs2_w; omega
  have h3Lv : 3 * ((L + 1) * vCap) < 2 ^ w := by dsimp only [s2] at hs2_w; omega
  have h2L1v : 2 * (L + 1) + vCap < 2 ^ w := by dsimp only [s2] at hs2_w; omega
  have hs2_diff : 3 * ((L + 1) * vCap) + (2 * (L + 1) + vCap) < 2 ^ w := by
    dsimp only [s2] at hs2_w; omega
  have hs3_diff : vCap + 3 * eCap < 2 ^ w := by dsimp only [s3] at hs3_w; omega
  let wrap {st₁ : State} {k₁ k₂ : ℕ}
      (h : ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k₂ + c ≤ T) (hk : k₁ ≤ k₂) :
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k₁ + c ≤ T :=
    let ⟨o, st', c, hr, hq, hc⟩ := h
    ⟨o, st', c, hr, hq, by omega⟩
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr2) h7v)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr3) h9e) h79)
        (by rw [← Nat.add_assoc, ← h_dg]; exact hdg_w))
      (by rw [h_dg, Nat.add_assoc])) ?_
  refine runs_seq_assign_le (v := s0)
    (Expr.eval_add
      (Expr.eval_add (Expr.eval_const (by rw [h_hdr]; omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h3dg)
        h6_3dg)
      (Expr.eval_add
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr3])) h3e)
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0])) (Expr.eval_const (by omega)) hL1)
          h2L1)
        h3e_2L1)
      hs0_w) ?_
  refine runs_seq_assign_le (v := s1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0])) (Expr.eval_const (by omega)) hL1)
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_mul
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0])) (Expr.eval_const (by omega)) hL1)
            (Expr.eval_reg_of_eq (by simp [hr3])) hLe)
          h2Le)
        hs1_diff)
      hs1_w) ?_
  refine runs_seq_assign_le (v := s2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_add
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_mul
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0])) (Expr.eval_const (by omega)) hL1)
            (Expr.eval_reg_of_eq (by simp [hr2])) hLv)
          h3Lv)
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0])) (Expr.eval_const (by omega)) hL1)
            h2L1)
          (Expr.eval_reg_of_eq (by simp [hr2]))
          h2L1v)
        hs2_diff)
      hs2_w) ?_
  refine runs_seq_assign_le (v := dsFixedSize L vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr2]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr3])) h3e)
          hs3_diff)
        hs3_w)
      hs3_eq) ?_
  refine wrap (hrest _ ⟨rfl, fun r hr => by
      simp [Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 9)],
    by simp, by simp⟩)
    (by simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega)

theorem dsInit_meetsContract {impl : SparsifyImpl} {mMax w L q vCap eCap : ℕ}
    {G : MGraph} {vL : List ℕ} {eEdges : List (ℕ × ℕ × ℕ)}
    {p : Program} {bOps bEdge bBatch bPhase bLW bSpDyn bInit : ℕ}
    {bSort bSplit bFwd bRevPrim bGT bRevCore bRevDyn bEmit bGuest bRev : ℕ}
    (hpInit : p.HasAt bInit (initProcs bOps bEdge bBatch bPhase bLW bSpDyn bInit))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpPhase : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev)) (hpRev : p.HasAt bRev (revProcs bOps bRev))
    (hpSpDyn : p.HasAt bSpDyn (sparsifyDynProcs impl.program.regBound impl.cw bFwd bRevDyn bGuest))
    (hpGuest : p.HasAt bGuest (sparsifyGuestProcs impl bGuest))
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpRevDyn : p.HasAt bRevDyn (gtRevDynProcs bOps bGT bRevCore))
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpGT : p.HasAt bGT (gtProcs bSort bOps)) (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (bInit + initIdx)
      (dsInitContract impl mMax w L q vCap eCap G vL eEdges) := by
  refine meetsContract_of_runs
    (hpInit.get (i := initIdx) (by simp [initProcs, initIdx]))
    fun args mem0 pos ω hargs hpre => ?_
  rcases hpre with ⟨V_ptr, E_ptr, b, rfl, hw16, hb1, hq1, hspace, hzb,
    h1m_w, hw'_le, hG_val, hGm_max, hG_v, hG_e, hVl_len, hVl_at, hVl_mem, hVp_lt, hEl_len,
    hEl_nd, hEl_at, hEl_inG, hG_inEl, hEp_lt⟩
  have hfix_w : dsFixedSize L vCap eCap < 2 ^ w := by omega
  have hheap_w : b + dsFixedSize L vCap eCap < 2 ^ w := by omega
  have hL_w : L < 2 ^ w := hargs L (by simp)
  have hq_w : q < 2 ^ w := hargs q (by simp)
  have hv_w : vCap < 2 ^ w := hargs vCap (by simp)
  have he_w : eCap < 2 ^ w := hargs eCap (by simp)
  have hVl_w : vL.length < 2 ^ w := hargs vL.length (by simp)
  have hVp_w : V_ptr < 2 ^ w := hargs V_ptr (by simp)
  have hEl_w : eEdges.length < 2 ^ w := hargs eEdges.length (by simp)
  have hEp_w : E_ptr < 2 ^ w := hargs E_ptr (by simp)
  have hb_w : b < 2 ^ w := hargs b (by simp)
  simp only [initProcs, initIdx, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsInitStmt]
  refine runs_start_le ?_
  refine dsInit_offset_cont hw16 hfix_w (by simp [startState]) (by simp [startState])
    (by simp [startState]) ?_
  rintro st1 ⟨hm1, hr_le8, hr9, hr10⟩
  have hpre_at : (dsInitAtContract impl mMax w L q 0 vCap eCap b G vL eEdges).pre
      [b, L, q, 0, vCap, eCap, vL.length, V_ptr, eEdges.length, E_ptr, b + dsFixedSize L vCap eCap]
      st1.mem := by
    rw [hm1]
    exact ⟨V_ptr, E_ptr, b + dsFixedSize L vCap eCap, rfl, hw16, hb1, hq1, by omega,
      le_rfl, hspace, hzb, h1m_w, hw'_le, hG_val, hGm_max, hG_v, hG_e, hVl_len, hVl_at,
      hVl_mem, hVp_lt, hEl_len, hEl_nd, hEl_at, hEl_inG, hG_inEl, hEp_lt⟩
  have hr0' : st1.regs 0 = L := (hr_le8 0 (by decide)).trans (by simp [startState])
  have hr1' : st1.regs 1 = q := (hr_le8 1 (by decide)).trans (by simp [startState])
  have hr2' : st1.regs 2 = vCap := (hr_le8 2 (by decide)).trans (by simp [startState])
  have hr3' : st1.regs 3 = eCap := (hr_le8 3 (by decide)).trans (by simp [startState])
  have hr4' : st1.regs 4 = vL.length := (hr_le8 4 (by decide)).trans (by simp [startState])
  have hr5' : st1.regs 5 = V_ptr := (hr_le8 5 (by decide)).trans (by simp [startState])
  have hr6' : st1.regs 6 = eEdges.length := (hr_le8 6 (by decide)).trans (by simp [startState])
  have hr7' : st1.regs 7 = E_ptr := (hr_le8 7 (by decide)).trans (by simp [startState])
  have hr8' : st1.regs 8 = b := (hr_le8 8 (by decide)).trans (by simp [startState])
  refine runs_seq_call_le (dsInitAt_meetsContract hpInit hpOps hpBatch hpPhase hpLW hpRev hpSpDyn
      hpGuest hpFwd hpEmit hpRevDyn hpRevCore hpRevPrim hpEdge hpGT hpSort)
    (by simp only [evalArgs, Expr.eval_reg_of_eq hr8', Expr.eval_reg_of_eq hr0',
        Expr.eval_reg_of_eq hr1', Expr.eval_const (by omega : (0 : ℕ) < 2 ^ w),
        Expr.eval_reg_of_eq hr2', Expr.eval_reg_of_eq hr3', Expr.eval_reg_of_eq hr4',
        Expr.eval_reg_of_eq hr5', Expr.eval_reg_of_eq hr6', Expr.eval_reg_of_eq hr7',
        Expr.eval_add (Expr.eval_reg_of_eq hr8') (Expr.eval_reg_of_eq hr10) hheap_w])
    (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_at ?_
  intro retFinal memFinal _ ⟨_, _, _, hEqAt, hrt_ge, hrt_le, hzF,
    ⟨x, hxV, hxE, hxIv, hxsL, hxm0, hx_hi, hxr0, hStateAt⟩, hfrF, hgenF⟩
  simp only [List.cons.injEq, and_true] at hEqAt
  rcases hEqAt with ⟨_, _, _, _, _, _, _, rfl, _, rfl, hhp_eq⟩
  rw [← hhp_eq] at hrt_ge hrt_le hxIv
  rw [hm1] at hfrF
  refine runs_ret_le (by simp [Expr.eval])
    ⟨V_ptr, E_ptr, b, rfl, hrt_ge, hrt_le, hzF,
      ⟨x, hxV, hxE, hxIv, hxsL, hStateAt, fun us =>
        revHistoryInv_zero G q (canonicalSparsify impl) us hxm0
          (fun v hv e => hxr0 v (hxV ▸ hv) e)
          (fun i hi => (hx_hi i hi).1)
          (fun i hi v hv => (hx_hi i hi).2 v (hxV ▸ hv))⟩,
      hfrF, hgenF⟩ ?_
  dsimp only [dsInitContract, dsInitAtContract, argsSize, Expr.size]
  omega

end

end MinCostFlow.DynSpanner.Program
