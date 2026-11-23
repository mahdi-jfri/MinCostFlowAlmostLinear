module

public import MinCostFlow.SparseCore.Program.CompBatchStepLift
import WordRAM.Tactic

/-!
# Edge-Insertion Step Primitives (`CompBatchStepInsBase`)

Defines `compStepInsDispStmt`, `compStepInsertProc`, and proves:
* `compStepInsDisp_runs`: conditional 1-insert dispatch on one component `c` (edgeful vs isolated).
* `compStepInsert_prefix_runs`: verification of the 18-statement common prefix of
  `compStepInsertProc` that decodes `[0, e, a, b]`, resolves `c1, c2`, and writes `edgeC1[e]`,
  `edgeC2[e]`, and `isIns[e]`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Procedures -/

/-- Conditional 1-insert dispatch on component in `reg rC` with endpoints `reg rA, reg rB`:
assumes `reg 0 = b`, `reg 3 = cntBase`, `reg 4 = updBuf`, `reg 5 = e`,
`reg 18 = compEdgefulBase`, `reg 19 = compEdgefulIdxBase`. Writes only registers `20, 23, 24`. -/
def compStepInsDispStmt (bDisp rC rA rB : ℕ) : Stmt :=
  .assign 23 (.load (.bin .add (.reg 18) (.reg rC))) ;;
  .cond (.reg 23)
    (.store (.reg 4) (.const 1) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.const 0) ;;
     .store (.bin .add (.reg 4) (.const 2)) (.reg 5) ;;
     .store (.bin .add (.reg 4) (.const 3)) (.reg rA) ;;
     .store (.bin .add (.reg 4) (.const 4)) (.reg rB) ;;
     .assign 24 (.load (.bin .add (.reg 19) (.reg rC))) ;;
     .call 20 bDisp [.reg 0, .reg 24, .reg 4, .const 5, .reg 3])
    .nop

/-- Common 18-statement prefix of `compStepInsertProc`: decodes `[0, e, a, b]`, resolves `c1, c2`,
writes `edgeC1[e], edgeC2[e], isIns[e]`, and loads base pointers into registers `5..19`. -/
def compStepInsPrefStmt : Stmt :=
  .assign 5 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 6 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 7 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const compOffECap))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const compOffVCompPtr))) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.reg 6))) ;;
  .assign 12 (.load (.bin .add (.reg 10) (.reg 7))) ;;
  .assign 13 (.load (.bin .add (.reg 0) (.const compOffEdgeC1Ptr))) ;;
  .store (.bin .add (.reg 13) (.reg 5)) (.reg 11) ;;
  .assign 14 (.load (.bin .add (.reg 0) (.const compOffEdgeC2Ptr))) ;;
  .store (.bin .add (.reg 14) (.reg 5)) (.reg 12) ;;
  .assign 15 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr))) ;;
  .store (.bin .add (.reg 15) (.reg 5)) (.const 1) ;;
  .assign 16 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr))) ;;
  .assign 17 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 18 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr))) ;;
  .assign 19 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr)))

/-- Same-component branch body of `compStepInsertProc`. -/
def compStepInsSameStmt (bMark bDisp : ℕ) : Stmt :=
  .assign 20 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr))) ;;
  .store (.bin .add (.reg 20) (.reg 5)) (.const 0) ;;
  .call 20 bMark [.reg 16, .reg 17, .reg 2, .reg 11] ;;
  compStepInsDispStmt bDisp 11 6 7

/-- Conditional 1-delete dispatch `[1, 1, e]` on component in `reg rC` (using `reg 18/19` from
`compStepInsPrefStmt`): assumes `reg 0 = b`, `reg 3 = cntBase`, `reg 4 = updBuf`, `reg 5 = e`,
`reg 18 = compEdgefulBase`, `reg 19 = compEdgefulIdxBase`. Writes only registers `20, 23, 24`. -/
def compStepInsDelOnlyDispStmt (bDisp rC : ℕ) : Stmt :=
  .assign 23 (.load (.bin .add (.reg 18) (.reg rC))) ;;
  .cond (.reg 23)
    (.store (.reg 4) (.const 1) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
     .store (.bin .add (.reg 4) (.const 2)) (.reg 5) ;;
     .assign 24 (.load (.bin .add (.reg 19) (.reg rC))) ;;
     .call 20 bDisp [.reg 0, .reg 24, .reg 4, .const 3, .reg 3])
    .nop

/-- Pre-dispatch prefix of the cross-component branch of `compStepInsertProc`: marks `isCross[e] := 1`
and marks both endpoint components touched (no ghost lists are populated, since cross-inserts are
projected to insert-then-delete self-loops). -/
def compStepInsCrossPreStmt (_bCons bMark : ℕ) : Stmt :=
  .assign 20 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr))) ;;
  .store (.bin .add (.reg 20) (.reg 5)) (.const 1) ;;
  .call 20 bMark [.reg 16, .reg 17, .reg 2, .reg 11] ;;
  .call 20 bMark [.reg 16, .reg 17, .reg 2, .reg 12]

/-- Cross-component branch body of `compStepInsertProc`: projects `.insert e a b`
to `[.insert e a a, .delete e]` on `c1` and `[.insert e b b, .delete e]` on `c2`. -/
def compStepInsCrossStmt (bCons bMark bDisp : ℕ) : Stmt :=
  compStepInsCrossPreStmt bCons bMark ;;
  (compStepInsDispStmt bDisp 11 6 6 ;; compStepInsDelOnlyDispStmt bDisp 11) ;;
  (compStepInsDispStmt bDisp 12 7 7 ;; compStepInsDelOnlyDispStmt bDisp 12)

/-- `args = [b, uPtr, heap, cntBase, updBuf]`: processes an encoded `.insert e a b` at `uPtr` and
returns `uPtr + 4`. -/
def compStepInsertProc (bCons bMark bDisp : ℕ) : Stmt :=
  compStepInsPrefStmt ;;
  .cond (.bin .eq (.reg 11) (.reg 12))
    (compStepInsSameStmt bMark bDisp)
    (compStepInsCrossStmt bCons bMark bDisp) ;;
  .ret (.bin .add (.reg 1) (.const 4))

lemma compStepInsertProc_noRand (bCons bMark bDisp : ℕ) :
    (compStepInsertProc bCons bMark bDisp).NoRand := by
  simp [compStepInsertProc, compStepInsPrefStmt, compStepInsSameStmt, compStepInsCrossStmt,
    compStepInsCrossPreStmt, compStepInsDispStmt, compStepInsDelOnlyDispStmt, Stmt.NoRand]

/-! ## 2. Conditional single-insert dispatch lemma -/

set_option maxHeartbeats 600000 in
/-- Verification of `compStepInsDispStmt`: dispatches `.insert e ua ub` to component `c` if edgeful,
or executes `.nop` if isolated, preserving registers `0..19` and `ZeroFrom st'.mem updBuf`. -/
lemma compStepInsDisp_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bDisp cntBase updBuf rC rA rB e ua ub : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k} {cnts : Fin k → ℕ}
    {st : State} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w) (hk : 1 ≤ k) (hLw : 1 ≤ x.L_w)
    (hrC_lt : rC < 20) (hrA_lt : rA < 20) (hrB_lt : rB < 20)
    (c : Fin x.numComps)
    (hefComp_inj : ∀ ec₁ ec₂ : Fin x.numEdgeful, x.edgefulComp ec₁ = x.edgefulComp ec₂ → ec₁ = ec₂)
    (hef_pos : ∀ ec : Fin x.numEdgeful, 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf (x.edgefulComp ec))).m)
    (hr0 : st.regs 0 = b) (hr3 : st.regs 3 = cntBase) (hr4 : st.regs 4 = updBuf)
    (hr5 : st.regs 5 = e) (hr18 : st.regs 18 = compEdgefulBase b x.vCap)
    (hr19 : st.regs 19 = compEdgefulIdxBase b x.vCap)
    (hrC : st.regs rC = c.1) (hrA : st.regs rA = ua) (hrB : st.regs rB = ub)
    (hnumC : x.numComps ≤ x.vCap)
    (hend_le : x.endAddr ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hbuf_w : updBuf + 5 < 2 ^ w)
    (hz : ZeroFrom st.mem updBuf)
    (hcnts_m : ∀ j : Fin k, st.mem (cntBase + j.1) = cnts j)
    (hTE : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr)
    (hef_m : st.mem (compEdgefulBase b x.vCap + c.1) =
      if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then 1 else 0)
    (hef_spec : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m →
      ∃ ec : Fin x.numEdgeful, x.edgefulIdx c = ec.1 ∧
        st.mem (compEdgefulIdxBase b x.vCap + c.1) = ec.1 ∧ x.edgefulComp ec = c ∧
        CompDispatchWinOk W k b S x ec st.mem)
    (hcap : ∀ j : Fin k,
      let Sj := (S j).compSt (x.compOf c)
      cnts j + ((applyLSFUpdate Sj (.insert e ua ub)).R_orig \ Sj.R_orig).card ≤ x.vCap)
    (hu_valid : ((S ⟨0, hk⟩).compSt (x.compOf c)).G.UpdateIsValid (.insert e ua ub))
    (heCap : e < x.eCap) (hua : ua < x.vCap) (hub : ub < x.vCap) :
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (cuts : Fin k → List (ℕ × ℕ)) (winConc' : Fin x.numEdgeful → Fin k → LSFConcrete),
      Runs w p ω (compStepInsDispStmt bDisp rC rA rB) st .normal st' cost ∧
      (∀ r < 20, st'.regs r = st.regs r) ∧
      (∀ j : Fin k,
        let Sj := (S j).compSt (x.compOf c)
        let Sj' := applyLSFUpdate Sj (.insert e ua ub)
        st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
        (∀ i (hi : i < (cuts j).length),
          st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
          st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
        (1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m →
          CompForestCutsValid x.vCap Sj.RF (cuts j) ∧
          ((cuts j).foldl compApplyForestCut Sj.RF).F.E = Sj'.RF.F.E ∧
          ((cuts j).map Prod.fst).Nodup ∧
          ((cuts j).map Prod.fst).toFinset = Sj.RF.F.E \ Sj'.RF.F.E ∧
          ((cuts j).map Prod.snd).Nodup ∧
          ((cuts j).map Prod.snd).toFinset = Sj'.RF.R \ Sj.RF.R) ∧
        ((compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m = 0 → cuts j = [])) ∧
      (∀ (ec : Fin x.numEdgeful) (j : Fin k),
        (x.edgefulComp ec = c →
          SameStaticConcrete (x.winConc ec j) (winConc' ec j) ∧
          (LSFRep W.h).rep (x.winHandle ec j) (applyLSFUpdate ((S j).compSt (x.compOf c)) (.insert e ua ub))
            (winConc' ec j) st'.mem) ∧
        (x.edgefulComp ec ≠ c → winConc' ec j = x.winConc ec j)) ∧
      (∀ a,
        (∀ ec j, x.edgefulComp ec = c → ¬ (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        a < updBuf → st'.mem a = st.mem a) ∧
      ZeroFrom st'.mem updBuf ∧
      (if _ : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then
        ∃ ec : Fin x.numEdgeful, x.edgefulComp ec = c ∧
          cost + 120 * (∑ j : Fin k, (cuts j).length) +
              (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) st'.mem) ≤
            k * (lsfBatchCostFactor * (5 * x.L_w + 1) + 850) + 320 +
              (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) st.mem)
      else cost ≤ 20 ∧ ∀ a, st'.mem a = st.mem a) := by
  classical
  intro rootsBase fDelBase
  have hef_w : compEdgefulBase b x.vCap + c.1 < 2 ^ w := by
    have h1 : compEdgefulBase b x.vCap + c.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase,
        compHdrSize]; have := c.2; omega
    omega
  have hefIdx_w : compEdgefulIdxBase b x.vCap + c.1 < 2 ^ w := by
    have h1 : compEdgefulIdxBase b x.vCap + c.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase,
        compEdgefulBase, compVCompBase, compHdrSize]; have := c.2; omega
    omega
  have he_w : e < 2 ^ w := by
    have h1 : x.eCap < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hua_w : ua < 2 ^ w := by
    have h1 : x.vCap < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hub_w : ub < 2 ^ w := by
    have h1 : x.vCap < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by intro h; subst h; simp at hw16
  set isEf := if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m then 1 else 0
  let st1 : State := { st with regs := Function.update st.regs 23 isEf }
  have hrun1 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 18) (.reg rC)))) st .normal st1 5 := by
    rw [runs_assign_iff]
    refine ⟨isEf, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [Expr.eval, BinOp.eval, hr18, hrC, hef_w, hef_m, isEf]
  by_cases hpos : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf c)).m
  · have hisEf : isEf = 1 := ite_eq_left hpos
    obtain ⟨ec, _, hec_m, hec_comp, hwin⟩ := hef_spec hpos
    have ⟨_, _, _, _, _, _, _, _, hW_ec, _⟩ := hwin
    have hst1_r : ∀ r < 20, st1.regs r = st.regs r := fun r hr =>
      Function.update_of_ne (by omega) _ _
    let m1 := Function.update st.mem updBuf 1
    let m2 := Function.update m1 (updBuf + 1) 0
    let m3 := Function.update m2 (updBuf + 2) e
    let m4 := Function.update m3 (updBuf + 3) ua
    let m5 := Function.update m4 (updBuf + 4) ub
    have hm5_lt : ∀ a < updBuf, m5 a = st.mem a := fun a ha => by
      simp [m5, m4, m3, m2, m1, Function.update_of_ne (show a ≠ updBuf + 4 by omega),
            Function.update_of_ne (show a ≠ updBuf + 3 by omega),
            Function.update_of_ne (show a ≠ updBuf + 2 by omega),
            Function.update_of_ne (show a ≠ updBuf + 1 by omega),
            Function.update_of_ne (show a ≠ updBuf by omega)]
    have hm5_ge : ∀ a ≥ updBuf + 5, m5 a = st.mem a := fun a ha => by
      simp [m5, m4, m3, m2, m1, Function.update_of_ne (show a ≠ updBuf + 4 by omega),
            Function.update_of_ne (show a ≠ updBuf + 3 by omega),
            Function.update_of_ne (show a ≠ updBuf + 2 by omega),
            Function.update_of_ne (show a ≠ updBuf + 1 by omega),
            Function.update_of_ne (show a ≠ updBuf by omega)]
    have hm5_0 : m5 updBuf = 1 := by simp [m5, m4, m3, m2, m1]
    have hm5_1 : m5 (updBuf + 1) = 0 := by simp [m5, m4, m3, m2]
    have hm5_2 : m5 (updBuf + 2) = e := by simp [m5, m4, m3]
    have hm5_3 : m5 (updBuf + 3) = ua := by simp [m5, m4]
    have hm5_4 : m5 (updBuf + 4) = ub := by simp [m5]
    let st2 : State := { st1 with mem := m1 }
    let st3 : State := { st1 with mem := m2 }
    let st4 : State := { st1 with mem := m3 }
    let st5 : State := { st1 with mem := m4 }
    let st6 : State := { st1 with mem := m5 }
    have hrun_s1 : Runs w p ω (.store (.reg 4) (.const 1)) st1 .normal st2 3 := by
      rw [runs_store_iff]; refine ⟨updBuf, 1, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
      · simp [Expr.eval, hst1_r 4 (by omega), hr4]
      · simp [Expr.eval, hw0]
    have hrun_s2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.const 0)) st2 .normal st3 5 := by
      rw [runs_store_iff]; refine ⟨updBuf + 1, 0, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, st2, hst1_r 4 (by omega), hr4, hw0, show updBuf + 1 < 2 ^ w by omega]
      · simp [Expr.eval]
    have hrun_s3 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.reg 5)) st3 .normal st4 5 := by
      rw [runs_store_iff]; refine ⟨updBuf + 2, e, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, st3, hst1_r 4 (by omega), hr4, hw2, show updBuf + 2 < 2 ^ w by omega]
      · simp [Expr.eval, st3, hst1_r 5 (by omega), hr5]
    have hrun_s4 : Runs w p ω (.store (.bin .add (.reg 4) (.const 3)) (.reg rA)) st4 .normal st5 5 := by
      rw [runs_store_iff]; refine ⟨updBuf + 3, ua, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, st4, hst1_r 4 (by omega), hr4, hw3, show updBuf + 3 < 2 ^ w by omega]
      · simp [Expr.eval, st4, hst1_r rA hrA_lt, hrA]
    have hrun_s5 : Runs w p ω (.store (.bin .add (.reg 4) (.const 4)) (.reg rB)) st5 .normal st6 5 := by
      rw [runs_store_iff]; refine ⟨updBuf + 4, ub, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, st5, hst1_r 4 (by omega), hr4, hw4, show updBuf + 4 < 2 ^ w by omega]
      · simp [Expr.eval, st5, hst1_r rB hrB_lt, hrB]
    have hefIdx_lt_buf : compEdgefulIdxBase b x.vCap + c.1 < updBuf := by
      have h1 : compEdgefulIdxBase b x.vCap + c.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase,
          compEdgefulBase, compVCompBase, compHdrSize]; have := c.2; omega
      omega
    let st7 : State := { st6 with regs := Function.update st6.regs 24 ec.1 }
    have hrun_a24 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 19) (.reg rC)))) st6 .normal st7 5 := by
      rw [runs_assign_iff]
      refine ⟨ec.1, ?_, rfl, rfl, by simp [Expr.size]⟩
      simp [Expr.eval, BinOp.eval, st6, hst1_r 19 (by omega), hr19, hst1_r rC hrC_lt, hrC,
        hefIdx_w, hm5_lt _ hefIdx_lt_buf, hec_m]
    have hwin5 : CompDispatchWinOk W k b S x ec m5 := by
      refine hwin.of_agree ⟨?_, ?_, ?_⟩ (fun j => ?_) (fun j a ha => ?_)
      · exact hm5_lt _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffK] at hTE ⊢; omega)
      · exact hm5_lt _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffVCap] at hTE ⊢; omega)
      · exact hm5_lt _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffHandlesPtr] at hTE ⊢; omega)
      · refine hm5_lt _ ?_
        have hlt : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) <
            compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
          dsimp only [compTablesEnd]
          have h1 : (ec.1 + 1) * k ≤ x.m0Total * k :=
            Nat.mul_le_mul_right k (by have := ec.2; omega)
          have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by
            rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
          omega
        omega
      · obtain ⟨_, _, _, _, _, _, hle⟩ := hW_ec j
        exact hm5_lt a (lt_of_lt_of_le ha.2 (le_trans hle (by omega)))
    have hwords5 : ∀ i < 1 + 4, m5 (updBuf + i) < 2 ^ w := fun i hi => by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simpa [hm5_0] using hw1
      · rw [hm5_1]; omega
      · rw [hm5_2]; exact he_w
      · rw [hm5_3]; exact hua_w
      · rw [hm5_4]; exact hub_w
    have hUpdAt5 : UpdateAt m5 (updBuf + 1)
        ((S ⟨0, hwin5.1⟩).compSt (x.compOf (x.edgefulComp ec))).G (.insert e ua ub) 4 := by
      refine ⟨rfl, fun i hi => ?_⟩
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
      rcases this with rfl | rfl | rfl | rfl <;>
        simp [Nat.add_assoc, hm5_1, hm5_2, hm5_3, hm5_4]
    obtain ⟨stD, cD, winConc_ec', cuts, hrunD, hbrD, hfrD, hzD, hcostD⟩ :=
      compDispatchOne_runs hpZero hpLogAdd hpPreLog hpLsf hw16 ec hwin5 (u_c := .insert e ua ub)
        hend_le hcnt_buf hbuf_w
        (fun a ha => (hm5_ge a ha).trans (hz a (by omega)))
        (fun j => (hm5_lt _ (by have := j.2; omega)).trans (hcnts_m j))
        (fun j => by simpa [hec_comp] using hcap j)
        hm5_0 hwords5 hUpdAt5 (by simpa [hec_comp] using hu_valid)
        heCap trivial
    let st8 : State := { st7 with regs := Function.update st7.regs 20 0, mem := stD.mem, pos := stD.pos }
    have hrun_call : Runs w p ω (.call 20 bDisp [.reg 0, .reg 24, .reg 4, .const 5, .reg 3])
        st7 .normal st8 (cD + 6) := by
      rw [runs_call_iff]
      refine ⟨[b, ec.1, updBuf, 5, cntBase], compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch),
        .returned 0, stD, cD, ?_, hpDisp, hrunD, rfl, ?_, by simp [Expr.size]; omega⟩
      · simp [evalArgs, Expr.eval, st7, st6, hst1_r 0 (by omega), hr0, hst1_r 4 (by omega), hr4,
          hst1_r 3 (by omega), hr3, hw5]
      · simp [st8, Outcome.value]
    let sThen : Stmt :=
      .store (.reg 4) (.const 1) ;;
      .store (.bin .add (.reg 4) (.const 1)) (.const 0) ;;
      .store (.bin .add (.reg 4) (.const 2)) (.reg 5) ;;
      .store (.bin .add (.reg 4) (.const 3)) (.reg rA) ;;
      .store (.bin .add (.reg 4) (.const 4)) (.reg rB) ;;
      .assign 24 (.load (.bin .add (.reg 19) (.reg rC))) ;;
      .call 20 bDisp [.reg 0, .reg 24, .reg 4, .const 5, .reg 3]
    have hrun_then : Runs w p ω sThen st1 .normal st8 (cD + 40) :=
      runs_seq_iff.mpr (Or.inr ⟨st2, 3, _, hrun_s1,
        runs_seq_iff.mpr (Or.inr ⟨st3, 5, _, hrun_s2,
        runs_seq_iff.mpr (Or.inr ⟨st4, 5, _, hrun_s3,
        runs_seq_iff.mpr (Or.inr ⟨st5, 5, _, hrun_s4,
        runs_seq_iff.mpr (Or.inr ⟨st6, 5, _, hrun_s5,
        runs_seq_iff.mpr (Or.inr ⟨st7, 5, cD + 6, hrun_a24, hrun_call, rfl⟩),
        rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
    have hrun_cond : Runs w p ω (.cond (.reg 23) sThen .nop) st1 .normal st8 (cD + 42) := by
      rw [runs_cond_iff]
      refine ⟨1, cD + 40, by simp [Expr.eval, st1, hisEf], ?_, by simp [Expr.size]; omega⟩
      simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
      exact hrun_then
    have hrun_all : Runs w p ω (compStepInsDispStmt bDisp rC rA rB) st .normal st8 (cD + 48) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, 5, cD + 42, hrun1, hrun_cond, by omega⟩)
    let winConc' : Fin x.numEdgeful → Fin k → LSFConcrete :=
      fun ec' j => if ec' = ec then winConc_ec' j else x.winConc ec' j
    have hphi_eq : (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) m5) =
        (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) st.mem) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      obtain ⟨_, _, _, _, _, _, hle⟩ := hW_ec j
      exact lsfPhi_congr fun a _ ha2 => hm5_lt a (lt_of_lt_of_le ha2 (le_trans hle (by omega)))
    refine ⟨st8, cD + 48, cuts, winConc', hrun_all, ?_, ?_, ?_, ?_, hzD, ?_⟩
    · intro r hr
      change Function.update (Function.update st1.regs 24 ec.1) 20 0 r = st.regs r
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hst1_r r hr]
    · intro j
      obtain ⟨_, _, hcnt', hlog', hval, hEeq, hndE, hsE, hndR, hsR⟩ := hbrD j
      dsimp only at hsR
      rw [hec_comp] at hval hEeq hsE hsR
      exact ⟨hcnt', hlog', fun _ => ⟨hval, hEeq, hndE, hsE, hndR, hsR⟩, fun hm0 => by omega⟩
    · intro ec' j
      constructor
      · intro hcomp
        have heq : ec' = ec := hefComp_inj ec' ec (hcomp.trans hec_comp.symm)
        subst heq; simp only [winConc', ↓reduceIte]
        obtain ⟨hss, hrep, _⟩ := hbrD j
        exact ⟨hss, by simpa [hec_comp] using hrep⟩
      · intro hne_c
        have hne_ec : ec' ≠ ec := fun h => hne_c (h ▸ hec_comp)
        simp [winConc', hne_ec]
    · intro a hfoot hcnt hrt hfd halt
      have hfoot_ec : ∀ j : Fin k, ¬ (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a :=
        fun j => hfoot ec j hec_comp
      exact (hfrD a hfoot_ec hcnt hrt hfd (Or.inl halt)).trans (hm5_lt a halt)
    · rw [dite_eq_left hpos]
      refine ⟨ec, hec_comp, ?_⟩
      simp only [winConc', ↓reduceIte]
      rw [hphi_eq] at hcostD
      have : 20 * (1 + 4) + 120 + 48 ≤ 320 := by omega
      linarith
  · have hisEf : isEf = 0 := ite_eq_right hpos
    let sThen : Stmt :=
      .store (.reg 4) (.const 1) ;;
      .store (.bin .add (.reg 4) (.const 1)) (.const 0) ;;
      .store (.bin .add (.reg 4) (.const 2)) (.reg 5) ;;
      .store (.bin .add (.reg 4) (.const 3)) (.reg rA) ;;
      .store (.bin .add (.reg 4) (.const 4)) (.reg rB) ;;
      .assign 24 (.load (.bin .add (.reg 19) (.reg rC))) ;;
      .call 20 bDisp [.reg 0, .reg 24, .reg 4, .const 5, .reg 3]
    have hrun_cond : Runs w p ω (.cond (.reg 23) sThen .nop) st1 .normal st1 3 := by
      rw [runs_cond_iff]
      refine ⟨0, 1, by simp [Expr.eval, st1, hisEf], ?_, by simp [Expr.size]⟩
      simp only [↓reduceIte]
      exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    have hrun_all : Runs w p ω (compStepInsDispStmt bDisp rC rA rB) st .normal st1 9 :=
      runs_seq_iff.mpr (Or.inr ⟨st1, 5, 3, hrun1, hrun_cond, rfl⟩)
    refine ⟨st1, 9, fun _ => [], x.winConc, hrun_all,
      fun r hr => Function.update_of_ne (by omega) _ _,
      fun j => ⟨by simpa using hcnts_m j, fun i hi => by simp at hi,
        fun h => absurd h hpos, fun _ => rfl⟩,
      fun ec j => ⟨fun h => absurd (h ▸ hef_pos ec) hpos, fun _ => rfl⟩,
      fun _ _ _ _ _ _ => rfl, hz, ?_⟩
    rw [dite_eq_right hpos]
    exact ⟨by omega, fun _ => rfl⟩

/-! ## 3. Common 18-statement prefix of `compStepInsertProc` -/

set_option maxHeartbeats 600000 in
/-- Executes `compStepInsPrefStmt`, decoding `[0, e, a, b]`, resolving `c1, c2`, storing
`edgeC1[e] := c1`, `edgeC2[e] := c2`, `isIns[e] := 1`, and populating registers `5..19`. -/
lemma compStepInsPref_runs {w k b uPtr heap cntBase updBuf e a bVert : ℕ}
    {p : Program} {x : CompLSFMeta k} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hTE : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr)
    (hend_w : x.endAddr < 2 ^ w) (hheap_w : heap + 1 < 2 ^ w) (hu_w : uPtr + 4 < 2 ^ w)
    (hhdr : compHeaderAt mem b x)
    (hu_in : mem (uPtr + 1) = e ∧ mem (uPtr + 2) = a ∧ mem (uPtr + 3) = bVert)
    (heCap : e < x.eCap) (ha_lt : a < x.vCap) (hb_lt : bVert < x.vCap)
    {c1 c2 : Fin x.numComps}
    (hva_m : mem (compVCompBase b + a) = c1.1) (hvb_m : mem (compVCompBase b + bVert) = c2.1) :
    let st0 := startState [b, uPtr, heap, cntBase, updBuf] mem pos
    let m1 := Function.update mem (compEdgeC1Base b x.vCap + e) c1.1
    let m2 := Function.update m1 (compEdgeC2Base b x.vCap x.eCap + e) c2.1
    let m3 := Function.update m2 (compIsInsBase b x.vCap x.eCap + e) 1
    let regsP :=
      Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
        st0.regs 5 e) 6 a) 7 bVert) 8 x.vCap) 9 x.eCap) 10 (compVCompBase b))
        11 c1.1) 12 c2.1) 13 (compEdgeC1Base b x.vCap)) 14 (compEdgeC2Base b x.vCap x.eCap))
        15 (compIsInsBase b x.vCap x.eCap)) 16 (compTouchMarkBase b x.vCap x.eCap))
        17 (heap + 1)) 18 (compEdgefulBase b x.vCap)) 19 (compEdgefulIdxBase b x.vCap)
    ∃ cP, Runs w p ω compStepInsPrefStmt st0 .normal { st0 with regs := regsP, mem := m3 } cP ∧
      cP ≤ 110 := by
  intro st0 m1 m2 m3 regsP
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := lt_of_le_of_lt hTE hend_w
  have hb_hdr_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hte_w ⊢; omega
  have h_off_w : ∀ off < compHdrSize, b + off < 2 ^ w := fun off hoff => by omega
  have hne_hdr : ∀ off < compHdrSize,
      b + off ≠ compEdgeC1Base b x.vCap + e ∧
      b + off ≠ compEdgeC2Base b x.vCap x.eCap + e ∧
      b + off ≠ compIsInsBase b x.vCap x.eCap + e := fun off hoff => by
    dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
      compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hoff ⊢
    exact ⟨by omega, by omega, by omega⟩
  have h_ec1_w : compEdgeC1Base b x.vCap + e < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC1Base, compM0Base,
      compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have h_ec2_w : compEdgeC2Base b x.vCap x.eCap + e < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC2Base, compEdgeC1Base,
      compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have h_ins_w : compIsInsBase b x.vCap x.eCap + e < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compIsInsBase, compIsCrossBase,
      compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
      compEdgefulBase, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have h_vca_w : compVCompBase b + a < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have h_vcb_w : compVCompBase b + bVert < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have hm3_fr : ∀ z, z ≠ compEdgeC1Base b x.vCap + e → z ≠ compEdgeC2Base b x.vCap x.eCap + e →
      z ≠ compIsInsBase b x.vCap x.eCap + e → m3 z = mem z := fun z h1 h2 h3 => by
    simp [m3, m2, m1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hw0 : w ≠ 0 := by intro h; subst h; simp at hw16
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw9 : 9 < 2 ^ w := by omega
  have hw10 : 10 < 2 ^ w := by omega
  have hw11 : 11 < 2 ^ w := by omega
  have hw14 : 14 < 2 ^ w := by omega
  have hw15 : 15 < 2 ^ w := by omega
  have hw17 : 17 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
  have hw19 : 19 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
  let st1 : State := { st0 with regs := Function.update st0.regs 5 e }
  let st2 : State := { st1 with regs := Function.update st1.regs 6 a }
  let st3 : State := { st2 with regs := Function.update st2.regs 7 bVert }
  let st4 : State := { st3 with regs := Function.update st3.regs 8 x.vCap }
  let st5 : State := { st4 with regs := Function.update st4.regs 9 x.eCap }
  let st6 : State := { st5 with regs := Function.update st5.regs 10 (compVCompBase b) }
  let st7 : State := { st6 with regs := Function.update st6.regs 11 c1.1 }
  let st8 : State := { st7 with regs := Function.update st7.regs 12 c2.1 }
  let st9 : State := { st8 with regs := Function.update st8.regs 13 (compEdgeC1Base b x.vCap) }
  let st10 : State := { st9 with mem := m1 }
  let st11 : State := { st10 with regs := Function.update st10.regs 14 (compEdgeC2Base b x.vCap x.eCap) }
  let st12 : State := { st11 with mem := m2 }
  let st13 : State := { st12 with regs := Function.update st12.regs 15 (compIsInsBase b x.vCap x.eCap) }
  let st14 : State := { st13 with mem := m3 }
  let st15 : State := { st14 with regs := Function.update st14.regs 16 (compTouchMarkBase b x.vCap x.eCap) }
  let st16 : State := { st15 with regs := Function.update st15.regs 17 (heap + 1) }
  let st17 : State := { st16 with regs := Function.update st16.regs 18 (compEdgefulBase b x.vCap) }
  have s1 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 1) (.const 1)))) st0 .normal st1 5 := by
    rw [runs_assign_iff]; refine ⟨e, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st0, startState, Expr.eval, BinOp.eval, hw0, show uPtr + 1 < 2 ^ w by omega, hu_in.1]
  have s2 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 1) (.const 2)))) st1 .normal st2 5 := by
    rw [runs_assign_iff]; refine ⟨a, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st1, st0, startState, Expr.eval, BinOp.eval, hw2, show uPtr + 2 < 2 ^ w by omega, hu_in.2.1]
  have s3 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 1) (.const 3)))) st2 .normal st3 5 := by
    rw [runs_assign_iff]; refine ⟨bVert, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, hw3, show uPtr + 3 < 2 ^ w by omega, hu_in.2.2]
  have hh_0 : mem b = x.vCap := by simpa [compOffVCap] using hhdr.1
  have hh_1 : mem (b + 1) = x.eCap := by simpa [compOffECap] using hhdr.2.1
  have hh_9 : mem (b + 9) = compVCompBase b := by simpa [compOffVCompPtr] using hhdr.2.2.2.2.2.2.2.2.2.1
  have hh_10 : mem (b + 10) = compEdgefulBase b x.vCap := by simpa [compOffEdgefulPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.1
  have hh_11 : mem (b + 11) = compEdgefulIdxBase b x.vCap := by simpa [compOffEdgefulIdxPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_14 : mem (b + 14) = compEdgeC1Base b x.vCap := by simpa [compOffEdgeC1Ptr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_15 : mem (b + 15) = compEdgeC2Base b x.vCap x.eCap := by simpa [compOffEdgeC2Ptr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_17 : mem (b + 17) = compIsInsBase b x.vCap x.eCap := by simpa [compOffIsInsPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_19 : mem (b + 19) = compTouchMarkBase b x.vCap x.eCap := by simpa [compOffTouchMarkPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have s4 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const compOffVCap)))) st3 .normal st4 5 := by
    rw [runs_assign_iff]; refine ⟨x.vCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, compOffVCap, show b < 2 ^ w by omega, hh_0]
  have s5 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const compOffECap)))) st4 .normal st5 5 := by
    rw [runs_assign_iff]; refine ⟨x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, compOffECap, hw0,
      h_off_w 1 (by decide), hh_1]
  have s6 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const compOffVCompPtr)))) st5 .normal st6 5 := by
    rw [runs_assign_iff]; refine ⟨compVCompBase b, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, compOffVCompPtr, hw9,
      h_off_w 9 (by decide), hh_9]
  have s7 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 10) (.reg 6)))) st6 .normal st7 5 := by
    rw [runs_assign_iff]; refine ⟨c1.1, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, h_vca_w, hva_m]
  have s8 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 10) (.reg 7)))) st7 .normal st8 5 := by
    rw [runs_assign_iff]; refine ⟨c2.1, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, h_vcb_w, hvb_m]
  have s9 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 0) (.const compOffEdgeC1Ptr)))) st8 .normal st9 5 := by
    rw [runs_assign_iff]; refine ⟨compEdgeC1Base b x.vCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval,
      compOffEdgeC1Ptr, hw14, h_off_w 14 (by decide), hh_14]
  have s10 : Runs w p ω (.store (.bin .add (.reg 13) (.reg 5)) (.reg 11)) st9 .normal st10 5 := by
    rw [runs_store_iff]; refine ⟨compEdgeC1Base b x.vCap + e, c1.1, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
    · simp [st9, st8, st7, st6, st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, h_ec1_w]
    · simp [st9, st8, st7, Expr.eval]
  have s11 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 0) (.const compOffEdgeC2Ptr)))) st10 .normal st11 5 := by
    rw [runs_assign_iff]; refine ⟨compEdgeC2Base b x.vCap x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval,
      compOffEdgeC2Ptr, hw15, h_off_w 15 (by decide), m1,
      Function.update_of_ne (hne_hdr 15 (by decide)).1, hh_15]
  have s12 : Runs w p ω (.store (.bin .add (.reg 14) (.reg 5)) (.reg 12)) st11 .normal st12 5 := by
    rw [runs_store_iff]; refine ⟨compEdgeC2Base b x.vCap x.eCap + e, c2.1, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
    · simp [st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, h_ec2_w]
    · simp [st11, st10, st9, st8, Expr.eval]
  have s13 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr)))) st12 .normal st13 5 := by
    rw [runs_assign_iff]; refine ⟨compIsInsBase b x.vCap x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h17 := hne_hdr 17 (by decide)
    simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState,
      Expr.eval, BinOp.eval, compOffIsInsPtr, hw17, h_off_w 17 (by decide), m2, m1,
      Function.update_of_ne h17.2.1, Function.update_of_ne h17.1, hh_17]
  have s14 : Runs w p ω (.store (.bin .add (.reg 15) (.reg 5)) (.const 1)) st13 .normal st14 5 := by
    rw [runs_store_iff]; refine ⟨compIsInsBase b x.vCap x.eCap + e, 1, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
    · simp [st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, h_ins_w]
    · simp [Expr.eval, hw0]
  have s15 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr)))) st14 .normal st15 5 := by
    rw [runs_assign_iff]; refine ⟨compTouchMarkBase b x.vCap x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h19 := hne_hdr 19 (by decide)
    simp [st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState,
      Expr.eval, BinOp.eval, compOffTouchMarkPtr, hw19, h_off_w 19 (by decide),
      hm3_fr _ h19.1 h19.2.1 h19.2.2, hh_19]
  have s16 : Runs w p ω (.assign 17 (.bin .add (.reg 2) (.const 1))) st15 .normal st16 4 := by
    rw [runs_assign_iff]; refine ⟨heap + 1, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0,
      startState, Expr.eval, BinOp.eval, hw0, hheap_w]
  have s17 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr)))) st16 .normal st17 5 := by
    rw [runs_assign_iff]; refine ⟨compEdgefulBase b x.vCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h10 := hne_hdr 10 (by decide)
    simp [st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0,
      startState, Expr.eval, BinOp.eval, compOffEdgefulPtr, hw10, h_off_w 10 (by decide),
      hm3_fr _ h10.1 h10.2.1 h10.2.2, hh_10]
  have s18 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr)))) st17 .normal
      { st0 with regs := regsP, mem := m3 } 5 := by
    rw [runs_assign_iff]; refine ⟨compEdgefulIdxBase b x.vCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h11 := hne_hdr 11 (by decide)
    simp [st17, st16, st15, st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0,
      startState, Expr.eval, BinOp.eval, compOffEdgefulIdxPtr, hw11, h_off_w 11 (by decide),
      hm3_fr _ h11.1 h11.2.1 h11.2.2, hh_11]
  refine ⟨106, ?_, by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, s1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s2,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s3,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s4,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s5,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s6,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s7,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s8,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s9,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s10,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s11,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s12,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s13,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s14,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s15,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s16,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s17, s18, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)

end

end MinCostFlow.SparseCore.Program
