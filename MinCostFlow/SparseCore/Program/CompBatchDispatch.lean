module

public import MinCostFlow.SparseCore.Program.CompBatchBase
public import MinCostFlow.SparseCore.Program.CompBatchLog
import WordRAM.Tactic

/-!
# Multi-Branch Logging LSF Dispatcher (`CompBatchDispatch`)

Defines and verifies `compDispatchOneProc (bZero bPreLog bLsfBatch : ℕ)`:
given `[b, ec, bufPtr, bufLen, cntBase]`, loops over all `k` branches `j < k` of edgeful component
`ec`, runs `compPreLogProc` to log every forest cut `(cutE, newRoot)` in order into branch `j`'s
`(rootsBuf_j, fDelBuf_j, cntBase + j)` scratch buffers, then dispatches the 1-update projected
batch at `[bufPtr, bufPtr + bufLen)` to `lsfModule`'s exact `lsfApplyBatchProc` at
`bLsf + lsfIdxBatch`, and finally zeroes `[bufPtr, bufPtr + bufLen)` via `compZeroRangeProc`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Procedure definition -/

/-- `args = [b, ec, bufPtr, bufLen, cntBase]`: applies the 1-update projected batch at
`[bufPtr, bufPtr + bufLen)` across all `k` branches of edgeful component `ec`, logging every
forest cut `(cutE, newRoot)` via `bPreLog` and updating each window via `bLsfBatch`, then zeroes
`[bufPtr, bufPtr + bufLen)` via `bZero`. Returns `0`. -/
def compDispatchOneProc (bZero bPreLog bLsfBatch : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
  .assign 8 (.bin .add (.reg 7) (.bin .mul (.reg 1) (.reg 5))) ;;
  .assign 9 (.bin .add (.reg 2) (.reg 3)) ;;
  .assign 10 (.bin .add (.reg 4) (.reg 5)) ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.reg 5) (.reg 6))) ;;
  .assign 12 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 13 (.const 0) ;;
  .loop (.bin .lt (.reg 13) (.reg 5))
    (.assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
     .assign 15 (.bin .mul (.reg 13) (.reg 6)) ;;
     .call 16 bPreLog
       [.reg 14, .reg 12, .bin .add (.reg 10) (.reg 15),
        .bin .add (.reg 11) (.reg 15), .bin .add (.reg 4) (.reg 13)] ;;
     .call 16 bLsfBatch [.reg 14, .reg 2, .reg 9] ;;
     .assign 13 (.bin .add (.reg 13) (.const 1))) ;;
  .call 16 bZero [.reg 2, .reg 3] ;;
  .ret (.const 0)

lemma compDispatchOneProc_noRand (bZero bPreLog bLsfBatch : ℕ) :
    (compDispatchOneProc bZero bPreLog bLsfBatch).NoRand := by
  simp [compDispatchOneProc, Stmt.NoRand]

/-! ## 2. Window-only dispatch precondition and verification -/

/-- Minimal window-only precondition for dispatching a single projected update to all `k` branches
of edgeful component `ec`. Independent of edge/ghost/touchMark tables so callers can update tables
first and dispatch windows afterward. -/
def CompDispatchWinOk (W : LSFWindowImpl) (k b : ℕ) (S : CompLSFFamily k) (x : CompLSFMeta k)
    (ec : Fin x.numEdgeful) (mem : ℕ → ℕ) : Prop :=
  ∃ hk : 1 ≤ k, 1 ≤ x.L_w ∧ x.numEdgeful ≤ x.m0Total ∧
    compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr ∧
    mem (b + compOffK) = k ∧ mem (b + compOffVCap) = x.vCap ∧
    mem (b + compOffHandlesPtr) = compHandlesBase b x.vCap x.eCap x.L_w ∧
    (∀ j : Fin k, ((S j).compSt (x.compOf (x.edgefulComp ec))).G =
      ((S ⟨0, hk⟩).compSt (x.compOf (x.edgefulComp ec))).G) ∧
    (∀ j : Fin k,
      let hWin := x.winHandle ec j
      let xWin := x.winConc ec j
      mem (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) = hWin ∧
      (LSFRep W.h).rep hWin ((S j).compSt (x.compOf (x.edgefulComp ec))) xWin mem ∧
      xWin.vCap = x.vCap ∧ xWin.eCap = x.eCap ∧ xWin.L_w = x.L_w ∧
      compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ hWin ∧
      xWin.endAddr hWin ≤ x.endAddr) ∧
    (∀ j₁ j₂ : Fin k, j₁ ≠ j₂ →
      ∀ a, (LSFRep W.h).foot (x.winHandle ec j₁) (x.winConc ec j₁) a →
        ¬ (LSFRep W.h).foot (x.winHandle ec j₂) (x.winConc ec j₂) a)

lemma CompLSFRepDirty.toDispatchWinOk {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {touched : List ℕ} {mem : ℕ → ℕ}
    (hrep : CompLSFRepDirty W k b S x touched mem) (ec : Fin x.numEdgeful) :
    CompDispatchWinOk W k b S x ec mem := by
  obtain ⟨hk, _, _, _, hLw, _, _, _, hne, hTE, hhdr, ⟨_, hBr⟩, _, _, _, _, _, _, _, _, _, _, hWins, hDisj⟩ := hrep
  exact ⟨hk, hLw, hne, hTE, hhdr.2.2.1, hhdr.1,
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun j => (hBr j).2.2.2.2.2.2 (x.edgefulComp ec),
    fun j => hWins ec j,
    fun j₁ j₂ hne' => hDisj ec ec j₁ j₂ (Or.inr hne')⟩

lemma CompDispatchWinOk.of_agree {W : LSFWindowImpl} {k b : ℕ} {S : CompLSFFamily k}
    {x : CompLSFMeta k} {ec : Fin x.numEdgeful} {mem mem' : ℕ → ℕ}
    (hwin : CompDispatchWinOk W k b S x ec mem)
    (hhdr : mem' (b + compOffK) = mem (b + compOffK) ∧
      mem' (b + compOffVCap) = mem (b + compOffVCap) ∧
      mem' (b + compOffHandlesPtr) = mem (b + compOffHandlesPtr))
    (hslots : ∀ j : Fin k, mem' (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) =
      mem (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)))
    (hwins : ∀ j : Fin k, ∀ a, (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a →
      mem' a = mem a) :
    CompDispatchWinOk W k b S x ec mem' := by
  obtain ⟨hk, hLw, hne, hTE, hK, hV, hH, hG, hW, hD⟩ := hwin
  refine ⟨hk, hLw, hne, hTE, hhdr.1.trans hK, hhdr.2.1.trans hV, hhdr.2.2.trans hH, hG, fun j => ?_, hD⟩
  obtain ⟨hs, hr, hv, he, hL, hge, hle⟩ := hW j
  exact ⟨(hslots j).trans hs, (lsfRep_local W.h _ _ _ mem mem' fun a ha => (hwins j a ha).symm).1 hr,
    hv, he, hL, hge, hle⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compDispatchOneProc`: updates all `k` branches of edgeful component `ec` by
applying `u_c`, appends each branch's ordered forest cuts `(cutE, newRoot)` to its cut-log
scratch buffers, zeroes `[bufPtr, bufPtr + 1 + len)`, and bounds amortized cost + potential
change while crediting `120` steps per logged cut. -/
theorem compDispatchOne_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bufPtr len cntBase : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {cnts : Fin k → ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hw16 : 16 ≤ 2 ^ w)
    (ec : Fin x.numEdgeful)
    (hwin : CompDispatchWinOk W k b S x ec mem)
    {u_c : Update}
    (hend_le : x.endAddr ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ bufPtr)
    (hbuf_w : bufPtr + (1 + len) < 2 ^ w)
    (hz : ZeroFrom mem (bufPtr + (1 + len)))
    (hcnts_m : ∀ j : Fin k, mem (cntBase + j.1) = cnts j)
    (hcap : ∀ j : Fin k,
      let Sj := (S j).compSt (x.compOf (x.edgefulComp ec))
      cnts j + ((applyLSFUpdate Sj u_c).R_orig \ Sj.R_orig).card ≤ x.vCap)
    (hnum : mem bufPtr = 1)
    (hwords : ∀ i < 1 + len, mem (bufPtr + i) < 2 ^ w)
    (hUpdAt : UpdateAt mem (bufPtr + 1) ((S ⟨0, hwin.1⟩).compSt (x.compOf (x.edgefulComp ec))).G u_c len)
    (hu_valid : ((S ⟨0, hwin.1⟩).compSt (x.compOf (x.edgefulComp ec))).G.UpdateIsValid u_c)
    (hu_caps : UpdateWithinCaps x.vCap x.eCap u_c)
    (hu_can : IsCanonUpd ((S ⟨0, hwin.1⟩).compSt (x.compOf (x.edgefulComp ec))).G u_c) :
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' c, ∃ (winConc' : Fin k → LSFConcrete) (cuts : Fin k → List (ℕ × ℕ)),
      Runs w p ω (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch))
        (startState [b, ec.1, bufPtr, 1 + len, cntBase] mem pos) (.returned 0) st' c ∧
      (∀ j : Fin k,
        let Sj := (S j).compSt (x.compOf (x.edgefulComp ec))
        let Sj' := applyLSFUpdate Sj u_c
        SameStaticConcrete (x.winConc ec j) (winConc' j) ∧
        (LSFRep W.h).rep (x.winHandle ec j) Sj' (winConc' j) st'.mem ∧
        st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
        (∀ i (hi : i < (cuts j).length),
          st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
          st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
        CompForestCutsValid x.vCap Sj.RF (cuts j) ∧
        ((cuts j).foldl compApplyForestCut Sj.RF).F.E = Sj'.RF.F.E ∧
        ((cuts j).map Prod.fst).Nodup ∧
        ((cuts j).map Prod.fst).toFinset = Sj.RF.F.E \ Sj'.RF.F.E ∧
        ((cuts j).map Prod.snd).Nodup ∧
        (match u_c with
         | .split _ v' _ _ =>
           Sj'.RF.R = insert v' (Sj.RF.R ∪ ((cuts j).map Prod.snd).toFinset) ∧
           v' ∉ Sj.RF.R ∪ ((cuts j).map Prod.snd).toFinset ∧
           ((cuts j).map Prod.snd).toFinset = Sj'.RF.R.erase v' \ Sj.RF.R
         | _ => ((cuts j).map Prod.snd).toFinset = Sj'.RF.R \ Sj.RF.R)) ∧
      (∀ a,
        (∀ j : Fin k, ¬ (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (a < bufPtr ∨ bufPtr + (1 + len) ≤ a) →
        st'.mem a = mem a) ∧
      ZeroFrom st'.mem bufPtr ∧
      c + 120 * (∑ j : Fin k, (cuts j).length) +
          (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' j) st'.mem) ≤
        k * (lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + 850) + 20 * (1 + len) + 120 +
          (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem) := by
  intro rootsBase fDelBase
  obtain ⟨hk, hLw, hne, hTE, hK_m, hVCap_m, hHPtr_m, hG_all, hWins_ec, hDisj_ec⟩ := hwin
  have hw0 : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hb_hdr_w : b + compHdrSize < 2 ^ w := by
    dsimp [compTablesEnd, compHandlesBase, compStaticSize, compGhostSize] at hTE; omega
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := by omega
  have hm0_pos : 1 ≤ x.m0Total := by have := ec.2; omega
  have heck_w : ec.1 * k < 2 ^ w := by
    dsimp [compTablesEnd] at hte_w
    have : ec.1 * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega); omega
  have hbase_w : compHandlesBase b x.vCap x.eCap x.L_w + ec.1 * k < 2 ^ w := by
    dsimp [compTablesEnd] at hte_w
    have : ec.1 * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega); omega
  have hk_w : k < 2 ^ w := by
    have : 1 * k ≤ x.m0Total * k := Nat.mul_le_mul_right k hm0_pos
    dsimp [compTablesEnd] at hte_w; omega
  have hvCap_w : x.vCap < 2 ^ w := by
    have : 1 * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap hk; omega
  set handlesBase := compHandlesBase b x.vCap x.eCap x.L_w
  set baseSlot := handlesBase + ec.1 * k
  set bufEnd := bufPtr + (1 + len)
  -- Prefix (9 assigns)
  let st0 := startState [b, ec.1, bufPtr, 1 + len, cntBase] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 5 k }
  let st2 : State := { st1 with regs := Function.update st1.regs 6 x.vCap }
  let st3 : State := { st2 with regs := Function.update st2.regs 7 handlesBase }
  let st4 : State := { st3 with regs := Function.update st3.regs 8 baseSlot }
  let st5 : State := { st4 with regs := Function.update st4.regs 9 bufEnd }
  let st6 : State := { st5 with regs := Function.update st5.regs 10 rootsBase }
  let st7 : State := { st6 with regs := Function.update st6.regs 11 fDelBase }
  let st8 : State := { st7 with regs := Function.update st7.regs 12 (bufPtr + 1) }
  let st9 : State := { st8 with regs := Function.update st8.regs 13 0 }
  have hp1 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const compOffK)))) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (by
      simp [st0, Expr.eval, BinOp.eval, startState,
        show compOffK < 2 ^ w by dsimp [compOffK, compHdrSize] at hb_hdr_w ⊢; omega,
        show b + compOffK < 2 ^ w by dsimp [compOffK, compHdrSize] at hb_hdr_w ⊢; omega]) hK_m,
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const compOffVCap)))) st1 .normal st2 5 :=
    runs_assign_iff.mpr ⟨x.vCap, Expr.eval_load_of_eq (by
      simp [st1, st0, Expr.eval, BinOp.eval, startState,
        show compOffVCap < 2 ^ w by dsimp [compOffVCap, compHdrSize] at hb_hdr_w ⊢; omega,
        show b + compOffVCap < 2 ^ w by dsimp [compOffVCap, compHdrSize] at hb_hdr_w ⊢; omega]) hVCap_m,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr)))) st2 .normal st3 5 :=
    runs_assign_iff.mpr ⟨handlesBase, Expr.eval_load_of_eq (by
      simp [st2, st1, st0, Expr.eval, BinOp.eval, startState,
        show compOffHandlesPtr < 2 ^ w by dsimp [compOffHandlesPtr, compHdrSize] at hb_hdr_w ⊢; omega,
        show b + compOffHandlesPtr < 2 ^ w by dsimp [compOffHandlesPtr, compHdrSize] at hb_hdr_w ⊢; omega])
      hHPtr_m, rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.bin .mul (.reg 1) (.reg 5)))) st3 .normal st4 6 :=
    runs_assign_iff.mpr ⟨baseSlot, by simp [st3, st2, st1, st0, Expr.eval, BinOp.eval, startState, handlesBase, baseSlot, heck_w, hbase_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 9 (.bin .add (.reg 2) (.reg 3))) st4 .normal st5 4 :=
    runs_assign_iff.mpr ⟨bufEnd, by simp [st4, st3, st2, st1, st0, Expr.eval, BinOp.eval, startState, bufEnd, hbuf_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 10 (.bin .add (.reg 4) (.reg 5))) st5 .normal st6 4 :=
    runs_assign_iff.mpr ⟨rootsBase, by simp [st5, st4, st3, st2, st1, st0, Expr.eval, BinOp.eval, startState, rootsBase, show cntBase + k < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.bin .mul (.reg 5) (.reg 6)))) st6 .normal st7 6 :=
    runs_assign_iff.mpr ⟨fDelBase, by simp [st6, st5, st4, st3, st2, st1, st0, Expr.eval, BinOp.eval, rootsBase, fDelBase,
      show k * x.vCap < 2 ^ w by omega, show cntBase + k + k * x.vCap < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp8 : Runs w p ω (.assign 12 (.bin .add (.reg 2) (.const 1))) st7 .normal st8 4 :=
    runs_assign_iff.mpr ⟨bufPtr + 1, by simp [st7, st6, st5, st4, st3, st2, st1, st0, Expr.eval, BinOp.eval, startState, hw1, show bufPtr + 1 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp9 : Runs w p ω (.assign 13 (.const 0)) st8 .normal st9 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  -- Loop over `j = 0 .. k - 1`
  let rootSpec : LSFState → LSFState → List (ℕ × ℕ) → Prop := fun St St' cs =>
    match u_c with
    | .split _ v' _ _ =>
      St'.RF.R = insert v' (St.RF.R ∪ (cs.map Prod.snd).toFinset) ∧
      v' ∉ St.RF.R ∪ (cs.map Prod.snd).toFinset ∧
      (cs.map Prod.snd).toFinset = St'.RF.R.erase v' \ St.RF.R
    | _ => (cs.map Prod.snd).toFinset = St'.RF.R \ St.RF.R
  let loopBody : Stmt :=
    .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
    .assign 15 (.bin .mul (.reg 13) (.reg 6)) ;;
    .call 16 bPreLog [.reg 14, .reg 12, .bin .add (.reg 10) (.reg 15),
      .bin .add (.reg 11) (.reg 15), .bin .add (.reg 4) (.reg 13)] ;;
    .call 16 (bLsf + lsfIdxBatch) [.reg 14, .reg 2, .reg 9] ;;
    .assign 13 (.bin .add (.reg 13) (.const 1))
  have hloop : ∀ rem j (s : State) (wc : Fin k → LSFConcrete) (csL : Fin k → List (ℕ × ℕ)),
      j ≤ k → k - j = rem →
      s.regs 2 = bufPtr → s.regs 3 = 1 + len → s.regs 4 = cntBase →
      s.regs 5 = k → s.regs 6 = x.vCap → s.regs 8 = baseSlot →
      s.regs 9 = bufEnd → s.regs 10 = rootsBase → s.regs 11 = fDelBase →
      s.regs 12 = bufPtr + 1 → s.regs 13 = j →
      (∀ t : Fin k, t.1 < j →
        let St := (S t).compSt (x.compOf (x.edgefulComp ec))
        let St' := applyLSFUpdate St u_c
        SameStaticConcrete (x.winConc ec t) (wc t) ∧
        (LSFRep W.h).rep (x.winHandle ec t) St' (wc t) s.mem ∧
        s.mem (cntBase + t.1) = cnts t + (csL t).length ∧
        (∀ i (hi : i < (csL t).length),
          s.mem (rootsBase + t.1 * x.vCap + (cnts t + i)) = (csL t)[i].2 ∧
          s.mem (fDelBase + t.1 * x.vCap + (cnts t + i)) = (csL t)[i].1) ∧
        CompForestCutsValid x.vCap St.RF (csL t) ∧
        ((csL t).foldl compApplyForestCut St.RF).F.E = St'.RF.F.E ∧
        ((csL t).map Prod.fst).Nodup ∧
        ((csL t).map Prod.fst).toFinset = St.RF.F.E \ St'.RF.F.E ∧
        ((csL t).map Prod.snd).Nodup ∧
        rootSpec St St' (csL t)) →
      (∀ t : Fin k, j ≤ t.1 → wc t = x.winConc ec t ∧ csL t = []) →
      (∀ a,
        (∀ t : Fin k, t.1 < j → ¬ (LSFRep W.h).foot (x.winHandle ec t) (x.winConc ec t) a) →
        (∀ t : Fin k, t.1 < j → a ≠ cntBase + t.1) →
        (∀ t : Fin k, t.1 < j → a < rootsBase + t.1 * x.vCap + cnts t ∨
          rootsBase + t.1 * x.vCap + cnts t + (csL t).length ≤ a) →
        (∀ t : Fin k, t.1 < j → a < fDelBase + t.1 * x.vCap + cnts t ∨
          fDelBase + t.1 * x.vCap + cnts t + (csL t).length ≤ a) →
        s.mem a = mem a) →
      ∃ stL cL, ∃ (wc' : Fin k → LSFConcrete) (csL' : Fin k → List (ℕ × ℕ)),
        Runs w p ω (.loop (.bin .lt (.reg 13) (.reg 5)) loopBody) s .normal stL cL ∧
        stL.regs 2 = bufPtr ∧ stL.regs 3 = 1 + len ∧
        (∀ t : Fin k,
          let St := (S t).compSt (x.compOf (x.edgefulComp ec))
          let St' := applyLSFUpdate St u_c
          SameStaticConcrete (x.winConc ec t) (wc' t) ∧
          (LSFRep W.h).rep (x.winHandle ec t) St' (wc' t) stL.mem ∧
          stL.mem (cntBase + t.1) = cnts t + (csL' t).length ∧
          (∀ i (hi : i < (csL' t).length),
            stL.mem (rootsBase + t.1 * x.vCap + (cnts t + i)) = (csL' t)[i].2 ∧
            stL.mem (fDelBase + t.1 * x.vCap + (cnts t + i)) = (csL' t)[i].1) ∧
          CompForestCutsValid x.vCap St.RF (csL' t) ∧
          ((csL' t).foldl compApplyForestCut St.RF).F.E = St'.RF.F.E ∧
          ((csL' t).map Prod.fst).Nodup ∧
          ((csL' t).map Prod.fst).toFinset = St.RF.F.E \ St'.RF.F.E ∧
          ((csL' t).map Prod.snd).Nodup ∧
          rootSpec St St' (csL' t)) ∧
        (∀ a,
          (∀ t : Fin k, ¬ (LSFRep W.h).foot (x.winHandle ec t) (x.winConc ec t) a) →
          (∀ t : Fin k, a ≠ cntBase + t.1) →
          (∀ t : Fin k, a < rootsBase + t.1 * x.vCap + cnts t ∨
            rootsBase + t.1 * x.vCap + cnts t + (csL' t).length ≤ a) →
          (∀ t : Fin k, a < fDelBase + t.1 * x.vCap + cnts t ∨
            fDelBase + t.1 * x.vCap + cnts t + (csL' t).length ≤ a) →
          stL.mem a = mem a) ∧
        cL + 120 * (∑ t : Fin k, (csL' t).length) +
            (∑ t : Fin k, lsfPhi (x.winHandle ec t) (wc' t) stL.mem) ≤
          rem * (lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + 850) + 6 +
            120 * (∑ t : Fin k, (csL t).length) +
            (∑ t : Fin k, lsfPhi (x.winHandle ec t) (wc t) s.mem) := by
    intro rem
    induction rem with
    | zero =>
      intro j s wc csL hj hrem hr2 hr3 _ hr5 _ _ _ _ _ _ hr13 hdone _ hfr
      have hjk : j = k := by omega
      subst hjk
      exact ⟨s, 4, wc, csL,
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr13, hr5], rfl, rfl, by simp [Expr.size]⟩),
        hr2, hr3, fun t => hdone t t.2,
        fun a h1 h2 h3 h4 => hfr a (fun t _ => h1 t) (fun t _ => h2 t) (fun t _ => h3 t) (fun t _ => h4 t),
        by omega⟩
    | succ rem ih =>
      intro j s wc csL hj hrem hr2 hr3 hr4 hr5 hr6 hr8 hr9 hr10 hr11 hr12 hr13 hdone hrest hfr
      have hjlt : j < k := by omega
      let jf : Fin k := ⟨j, hjlt⟩
      obtain ⟨hslot_m, hrep_j, hvj, hej, hLwj, hge_j, hle_j⟩ := hWins_ec jf
      have hslot_lt : baseSlot + j < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
        dsimp [baseSlot, handlesBase, compTablesEnd]
        have : ec.1 * k + j < (ec.1 + 1) * k := by ring_nf; omega
        have : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
        omega
      have hjv_le : (j + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
      have hjv_eq : (j + 1) * x.vCap = j * x.vCap + x.vCap := by ring
      have hcuts_le : ∀ t : Fin k, t.1 < j → cnts t + (csL t).length ≤ x.vCap := by
        intro t ht
        have h1 := hcap t
        have hct := (List.toFinset_card_of_nodup (hdone t ht).2.2.2.2.2.2.2.2.1).symm
        rw [List.length_map] at hct
        have hsub : ((csL t).map Prod.snd).toFinset ⊆
            ((applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) u_c).R_orig \
              ((S t).compSt (x.compOf (x.edgefulComp ec))).R_orig) := by
          intro z hz; have h2 := (hdone t ht).2.2.2.2.2.2.2.2.2
          cases u_c with
          | split v v' St Sh =>
            rw [h2.2.2] at hz; rw [Finset.mem_sdiff, Finset.mem_erase] at hz
            have hiso : (applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) (.split v v' St Sh)).isolatedVerts =
                insert v' ((S t).compSt (x.compOf (x.edgefulComp ec))).isolatedVerts := rfl
            simp only [LSFState.RF, LSFState.R, hiso, Finset.mem_union, Finset.mem_insert] at hz
            exact Finset.mem_sdiff.mpr ⟨by tauto, fun h => hz.2 (Or.inl h)⟩
          | insert e a b_v =>
            rw [h2] at hz; rw [Finset.mem_sdiff] at hz
            have hiso : (applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) (.insert e a b_v)).isolatedVerts =
                ((S t).compSt (x.compOf (x.edgefulComp ec))).isolatedVerts := rfl
            simp only [LSFState.RF, LSFState.R, hiso, Finset.mem_union] at hz
            exact Finset.mem_sdiff.mpr ⟨by tauto, fun h => hz.2 (Or.inl h)⟩
          | delete e =>
            rw [h2] at hz; rw [Finset.mem_sdiff] at hz
            have hiso : (applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) (.delete e)).isolatedVerts =
                ((S t).compSt (x.compOf (x.edgefulComp ec))).isolatedVerts := rfl
            simp only [LSFState.RF, LSFState.R, hiso, Finset.mem_union] at hz
            exact Finset.mem_sdiff.mpr ⟨by tauto, fun h => hz.2 (Or.inl h)⟩
        have := Finset.card_le_card hsub; omega
      have hbuf_agr : ∀ i < 1 + len, s.mem (bufPtr + i) = mem (bufPtr + i) := fun i _ =>
        hfr (bufPtr + i)
          (fun t _ hft => by have := (hWins_ec t).2.2.2.2.2.2; have := hft.2; omega)
          (fun t _ => by have := t.2; omega)
          (fun t ht => Or.inr (by
            have := hcuts_le t ht
            have ht_le : (t.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
            have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
            omega))
          (fun t ht => Or.inr (by
            have := hcuts_le t ht
            have ht_le : (t.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
            have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
            omega))
      have hslot_s : s.mem (baseSlot + j) = x.winHandle ec jf := by
        have hag := hfr (baseSlot + j)
          (fun t _ hft => by have := (hWins_ec t).2.2.2.2.2.1; have := hft.1; omega)
          (fun t _ => by omega) (fun t _ => Or.inl (by omega)) (fun t _ => Or.inl (by omega))
        rw [hag, show baseSlot + j = handlesBase + (ec.1 * k + j) by dsimp [baseSlot]; omega]
        exact hslot_m
      have hcnt_js : s.mem (cntBase + j) = cnts jf := by
        have hag := hfr (cntBase + j)
          (fun t _ hft => by have := (hWins_ec t).2.2.2.2.2.2; have := hft.2; omega)
          (fun t ht => by omega) (fun t _ => Or.inl (by omega)) (fun t _ => Or.inl (by omega))
        exact hag.trans (hcnts_m jf)
      have hrep_js : (LSFRep W.h).rep (x.winHandle ec jf) ((S jf).compSt (x.compOf (x.edgefulComp ec)))
          (x.winConc ec jf) s.mem :=
        (lsfRep_local W.h _ _ _ mem s.mem fun a ha =>
          (hfr a (fun t ht => hDisj_ec jf t (fun h => by
              have := congrArg Fin.val h; dsimp [jf] at this; omega) a ha)
            (fun t _ => by have := ha.2; omega)
            (fun t _ => Or.inl (by have := ha.2; omega))
            (fun t _ => Or.inl (by have := ha.2; omega))).symm).1 hrep_j
      have hG_eq : ((S jf).compSt (x.compOf (x.edgefulComp ec))).G =
          ((S ⟨0, hk⟩).compSt (x.compOf (x.edgefulComp ec))).G :=
        hG_all jf
      have hUpd_s : UpdateAt s.mem (bufPtr + 1) ((S jf).compSt (x.compOf (x.edgefulComp ec))).G u_c len := by
        rw [hG_eq]
        exact UpdateAt.of_agree hUpdAt fun i hi => by simpa [Nat.add_assoc] using hbuf_agr (1 + i) (by omega)
      -- Call `compPreLog` on branch `jf`
      have hbuf_jf : CutLogBufOk w (x.winHandle ec jf) ((x.winConc ec jf).endAddr (x.winHandle ec jf))
          (rootsBase + j * x.vCap) (fDelBase + j * x.vCap) (cntBase + j) x.vCap := by
        refine ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inl (by omega),
          Or.inl (by omega), Or.inl (by omega), by omega, by omega, by omega, hvCap_w⟩
      obtain ⟨stP, cP, xP, S_pre, cutsP, hrP, hsP, hrepP, hGP_eq, happP, hFEP, hRP, hlenP,
        hcntP, hlogP, hfrP, hvP, hfP, hndEP, hsEP, hndRP, hsRP, hcP⟩ :=
        compPreLog_runs (pos := s.pos) (ω := ω) hpLsf hpLogAdd hw16 (by omega) (by omega)
          (fun i _ => Or.inr (by omega))
          (fun i _ => ⟨by omega, Or.inr (by omega), Or.inr (by omega)⟩)
          hbuf_jf hcnt_js hrep_js hUpd_s (hG_eq ▸ hu_valid) (hcap jf)
      have hcntP_le : cnts jf + cutsP.length ≤ x.vCap := by have := hcap jf; omega
      have hbuf_agrP : ∀ i < 1 + len, stP.mem (bufPtr + i) = mem (bufPtr + i) := fun i hi =>
        (hfrP (bufPtr + i) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans (hbuf_agr i hi)
      have hz_P : ZeroFrom stP.mem bufEnd := fun a ha =>
        (hfrP a (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))).trans
          ((hfr a (fun t _ hft => by have := (hWins_ec t).2.2.2.2.2.2; have := hft.2; omega)
            (fun t _ => by have := t.2; omega)
            (fun t ht => Or.inr (by
              have := hcuts_le t ht
              have ht_le : (t.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
              have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
              omega))
            (fun t ht => Or.inr (by
              have := hcuts_le t ht
              have ht_le : (t.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
              have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
              omega))).trans (hz a ha))
      -- Call `lsfApplyBatch` on `S_pre`
      have hUpd_P : UpdateAt stP.mem (bufPtr + 1) S_pre.G u_c len := by
        rw [hGP_eq, hG_eq]
        exact UpdateAt.of_agree hUpdAt fun i hi => by simpa [Nat.add_assoc] using hbuf_agrP (1 + i) (by omega)
      have hcaps_P : UpdateWithinCaps xP.vCap xP.eCap u_c := by
        rw [hsP.1, hsP.2.1, hvj, hej]; exact hu_caps
      have hLw_P : 1 ≤ xP.L_w := by rw [hsP.2.2.2.2.2.2.2.2.1, hLwj]; exact hLw
      obtain ⟨bodyB, hbodyB, stB, cB, xB, hrB, hsB, hrepB, hfrB, hcB⟩ :=
        lsfApplyBatch_single_runs_of_hasAt (heap := bufEnd) stP.pos ω hpLsf hw16 hLw_P
          (by rw [hsP.endAddr]; omega) (by omega) (by omega)
          (fun i _ => Or.inr (by rw [hsP.endAddr]; omega))
          (fun i hi => (hbuf_agrP i hi).symm ▸ hwords i hi)
          hrepP (by simpa using (hbuf_agrP 0 (by omega)).trans hnum)
          hUpd_P (hGP_eq.symm ▸ hG_eq ▸ hu_valid) hcaps_P (hGP_eq.symm ▸ hG_eq ▸ hu_can)
      rw [happP] at hrepB
      have hfr_step : ∀ a,
          (a < x.winHandle ec jf ∨ (x.winConc ec jf).endAddr (x.winHandle ec jf) ≤ a) →
          a ≠ cntBase + j →
          (a < rootsBase + j * x.vCap + cnts jf ∨ rootsBase + j * x.vCap + cnts jf + cutsP.length ≤ a) →
          (a < fDelBase + j * x.vCap + cnts jf ∨ fDelBase + j * x.vCap + cnts jf + cutsP.length ≤ a) →
          stB.mem a = s.mem a := fun a ha hnc hnr hnf =>
        (hfrB a (by rw [hsP.endAddr]; exact ha)).trans (hfrP a ha hnc hnr hnf)
      -- Assemble 1 iteration of `loopBody`
      let s1 : State := { s with regs := Function.update s.regs 14 (x.winHandle ec jf) }
      let s2 : State := { s1 with regs := Function.update s1.regs 15 (j * x.vCap) }
      let s3 : State := { mem := stP.mem, regs := Function.update s2.regs 16 0, pos := stP.pos }
      let s4 : State := { mem := stB.mem, regs := Function.update s3.regs 16 bufEnd, pos := stB.pos }
      let s5 : State := { s4 with regs := Function.update s4.regs 13 (j + 1) }
      have hb1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 8) (.reg 13)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨x.winHandle ec jf, Expr.eval_load_of_eq
          (by simp [Expr.eval, BinOp.eval, hr8, hr13, show baseSlot + j < 2 ^ w by omega]) hslot_s,
          rfl, rfl, by simp [Expr.size]⟩
      have hb2 : Runs w p ω (.assign 15 (.bin .mul (.reg 13) (.reg 6))) s1 .normal s2 4 :=
        runs_assign_iff.mpr ⟨j * x.vCap, by simp [s1, Expr.eval, BinOp.eval, hr13, hr6, show j * x.vCap < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hb3 : Runs w p ω (.call 16 bPreLog [.reg 14, .reg 12, .bin .add (.reg 10) (.reg 15),
          .bin .add (.reg 11) (.reg 15), .bin .add (.reg 4) (.reg 13)]) s2 .normal s3 (11 + cP + 1) :=
        runs_call_iff.mpr ⟨[x.winHandle ec jf, bufPtr + 1, rootsBase + j * x.vCap, fDelBase + j * x.vCap, cntBase + j],
          _, .returned 0, stP, cP,
          by simp [s2, s1, evalArgs, Expr.eval, BinOp.eval, hr12, hr10, hr11, hr4, hr13,
            show rootsBase + j * x.vCap < 2 ^ w by omega, show fDelBase + j * x.vCap < 2 ^ w by omega,
            show cntBase + j < 2 ^ w by omega],
          hpPreLog, hrP, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hb4 : Runs w p ω (.call 16 (bLsf + lsfIdxBatch) [.reg 14, .reg 2, .reg 9]) s3 .normal s4 (3 + cB + 1) :=
        runs_call_iff.mpr ⟨[x.winHandle ec jf, bufPtr, bufEnd], bodyB, .returned bufEnd, stB, cB,
          by simp [s3, s2, s1, evalArgs, Expr.eval, hr2, hr9], hbodyB, hrB, rfl, rfl, by simp [argsSize, Expr.size]⟩
      have hb5 : Runs w p ω (.assign 13 (.bin .add (.reg 13) (.const 1))) s4 .normal s5 4 :=
        runs_assign_iff.mpr ⟨j + 1, by simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr13, hw1, show j + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω loopBody s .normal s5 (cP + cB + 33) :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 5, cP + cB + 27, hb1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 4, cP + cB + 22, hb2,
            runs_seq_iff.mpr (Or.inr ⟨s3, 11 + cP + 1, cB + 9, hb3,
              runs_seq_iff.mpr (Or.inr ⟨s4, 3 + cB + 1, 4, hb4, hb5, by omega⟩), by omega⟩), by omega⟩), by omega⟩)
      -- Update `wc` and `csL` at `jf` and apply IH
      let wc1 := Function.update wc jf xB
      let csL1 := Function.update csL jf cutsP
      have hdone1 : ∀ t : Fin k, t.1 < j + 1 →
          let St := (S t).compSt (x.compOf (x.edgefulComp ec))
          let St' := applyLSFUpdate St u_c
          SameStaticConcrete (x.winConc ec t) (wc1 t) ∧
          (LSFRep W.h).rep (x.winHandle ec t) St' (wc1 t) s5.mem ∧
          s5.mem (cntBase + t.1) = cnts t + (csL1 t).length ∧
          (∀ i (hi : i < (csL1 t).length),
            s5.mem (rootsBase + t.1 * x.vCap + (cnts t + i)) = (csL1 t)[i].2 ∧
            s5.mem (fDelBase + t.1 * x.vCap + (cnts t + i)) = (csL1 t)[i].1) ∧
          CompForestCutsValid x.vCap St.RF (csL1 t) ∧
          ((csL1 t).foldl compApplyForestCut St.RF).F.E = St'.RF.F.E ∧
          ((csL1 t).map Prod.fst).Nodup ∧
          ((csL1 t).map Prod.fst).toFinset = St.RF.F.E \ St'.RF.F.E ∧
          ((csL1 t).map Prod.snd).Nodup ∧
          rootSpec St St' (csL1 t) := by
        intro t ht
        by_cases htj : t = jf
        · subst htj
          have hwc_eq : wc1 jf = xB := Function.update_self jf xB wc
          have hcs_eq : csL1 jf = cutsP := Function.update_self jf cutsP csL
          rw [hwc_eq, hcs_eq]
          refine ⟨hsP.trans hsB, hrepB, (hfrB (cntBase + j) (Or.inr (by rw [hsP.endAddr]; omega))).trans hcntP,
            fun i hi => ⟨(hfrB _ (Or.inr (by rw [hsP.endAddr]; omega))).trans (hlogP i hi).1,
              (hfrB _ (Or.inr (by rw [hsP.endAddr]; omega))).trans (hlogP i hi).2⟩,
            hvj ▸ hvP, by rw [hfP, hFEP], hndEP, by rw [hsEP, hFEP], hndRP, ?_⟩
          dsimp only [rootSpec]
          cases u_c with
          | split _ v' _ _ =>
            have hR_sub : ((S jf).compSt (x.compOf (x.edgefulComp ec))).RF.R ⊆ S_pre.RF.R := by
              rw [← hfP]
              have hsub : ∀ (l : List (ℕ × ℕ)) (RF : RootedForest), RF.R ⊆ (l.foldl compApplyForestCut RF).R := by
                intro l; induction l with
                | nil => intro _; exact Finset.Subset.refl _
                | cons p tl ih => intro RF; exact Finset.Subset.trans (Finset.subset_insert p.2 RF.R) (ih (compApplyForestCut RF p))
              exact hsub cutsP _
            have hR_un : ((S jf).compSt (x.compOf (x.edgefulComp ec))).RF.R ∪ (cutsP.map Prod.snd).toFinset = S_pre.RF.R := by
              rw [hsRP]; exact Finset.union_sdiff_of_subset hR_sub
            refine ⟨hR_un.symm ▸ hRP.1, hR_un.symm ▸ hRP.2, ?_⟩
            rw [hRP.1, Finset.erase_insert hRP.2, hsRP]
          | insert _ _ _ => rw [hRP, hsRP]
          | delete _ => rw [hRP, hsRP]
        · have htlt : t.1 < j := by have : t.1 ≠ j := fun h => htj (Fin.ext h); omega
          have hwc_eq : wc1 t = wc t := Function.update_of_ne htj xB wc
          have hcs_eq : csL1 t = csL t := Function.update_of_ne htj cutsP csL
          rw [hwc_eq, hcs_eq]
          obtain ⟨hs_t, hrep_t, hcnt_t, hlog_t, hv_t, hf_t, hndE_t, hsE_t, hndR_t, hsR_t⟩ := hdone t htlt
          have ht_le : (t.1 + 1) * x.vCap ≤ j * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
          have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
          have hcl_t := hcuts_le t htlt
          have hrep_t' : (LSFRep W.h).rep (x.winHandle ec t) _ (wc t) s5.mem :=
            (lsfRep_local W.h _ _ _ s.mem s5.mem fun a ha => by
              have ha0 : (LSFRep W.h).foot (x.winHandle ec t) (x.winConc ec t) a := by
                dsimp [LSFRep] at ha ⊢; rw [← hs_t.endAddr]; exact ha
              have hdj := hDisj_ec t jf htj a ha0
              have ha_out : a < x.winHandle ec jf ∨ (x.winConc ec jf).endAddr (x.winHandle ec jf) ≤ a := by
                dsimp [LSFRep] at hdj; omega
              have ha_le : a < x.endAddr := by have := (hWins_ec t).2.2.2.2.2.2; exact lt_of_lt_of_le ha0.2 this
              exact (hfr_step a ha_out (by omega) (Or.inl (by omega)) (Or.inl (by omega))).symm).1 hrep_t
          refine ⟨hs_t, hrep_t',
            (hfr_step (cntBase + t.1) (Or.inr (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans hcnt_t,
            fun i hi => ⟨(hfr_step _ (Or.inr (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (hlog_t i hi).1,
              (hfr_step _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (hlog_t i hi).2⟩,
            hv_t, hf_t, hndE_t, hsE_t, hndR_t, by cases u_c <;> exact hsR_t⟩
      have hrest1 : ∀ t : Fin k, j + 1 ≤ t.1 → wc1 t = x.winConc ec t ∧ csL1 t = [] := by
        intro t ht
        have hne : t ≠ jf := fun h => by have := congrArg Fin.val h; dsimp [jf] at this; omega
        dsimp only [wc1, csL1]; rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact hrest t (by omega)
      have hfr1 : ∀ a,
          (∀ t : Fin k, t.1 < j + 1 → ¬ (LSFRep W.h).foot (x.winHandle ec t) (x.winConc ec t) a) →
          (∀ t : Fin k, t.1 < j + 1 → a ≠ cntBase + t.1) →
          (∀ t : Fin k, t.1 < j + 1 → a < rootsBase + t.1 * x.vCap + cnts t ∨
            rootsBase + t.1 * x.vCap + cnts t + (csL1 t).length ≤ a) →
          (∀ t : Fin k, t.1 < j + 1 → a < fDelBase + t.1 * x.vCap + cnts t ∨
            fDelBase + t.1 * x.vCap + cnts t + (csL1 t).length ≤ a) →
          s5.mem a = mem a := by
        intro a h1 h2 h3 h4
        have h1j : a < x.winHandle ec jf ∨ (x.winConc ec jf).endAddr (x.winHandle ec jf) ≤ a := by
          have := h1 jf (by dsimp [jf]; omega); dsimp [LSFRep] at this; omega
        have h3j := h3 jf (by dsimp [jf]; omega); dsimp only [csL1] at h3j; rw [Function.update_self] at h3j
        have h4j := h4 jf (by dsimp [jf]; omega); dsimp only [csL1] at h4j; rw [Function.update_self] at h4j
        refine (hfr_step a h1j (h2 jf (by dsimp [jf]; omega)) h3j h4j).trans ?_
        exact hfr a (fun t ht => h1 t (by omega)) (fun t ht => h2 t (by omega))
          (fun t ht => by
            have hne : t ≠ jf := fun h => by have := congrArg Fin.val h; dsimp [jf] at this; omega
            have := h3 t (by omega); dsimp only [csL1] at this; rwa [Function.update_of_ne hne] at this)
          (fun t ht => by
            have hne : t ≠ jf := fun h => by have := congrArg Fin.val h; dsimp [jf] at this; omega
            have := h4 t (by omega); dsimp only [csL1] at this; rwa [Function.update_of_ne hne] at this)
      obtain ⟨stL, cL, wc', csL', hrL, hrL2, hrL3, hdoneL, hfrL, hcL⟩ :=
        ih (j + 1) s5 wc1 csL1 (by omega) (by omega)
          (by simp [s5, s4, s3, s2, s1, hr2]) (by simp [s5, s4, s3, s2, s1, hr3])
          (by simp [s5, s4, s3, s2, s1, hr4]) (by simp [s5, s4, s3, s2, s1, hr5])
          (by simp [s5, s4, s3, s2, s1, hr6]) (by simp [s5, s4, s3, s2, s1, hr8])
          (by simp [s5, s4, s3, s2, s1, hr9]) (by simp [s5, s4, s3, s2, s1, hr10])
          (by simp [s5, s4, s3, s2, s1, hr11]) (by simp [s5, s4, s3, s2, s1, hr12])
          (by simp [s5]) hdone1 hrest1 hfr1
      have hcond : (Expr.bin .lt (.reg 13) (.reg 5)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr13, hr5, hjlt, hw1]
      -- Potential & cut-count telescope across branch `jf`
      have hsum_cuts : (∑ t : Fin k, (csL1 t).length) = (∑ t : Fin k, (csL t).length) + cutsP.length := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jf),
          ← Finset.add_sum_erase _ (fun t => (csL t).length) (Finset.mem_univ jf)]
        have hrest_j : (csL jf).length = 0 := by rw [(hrest jf (by dsimp [jf]; omega)).2]; rfl
        have hupd_j : (csL1 jf).length = cutsP.length := by dsimp only [csL1]; rw [Function.update_self]
        have hrest_eq : ∑ t ∈ Finset.univ.erase jf, (csL1 t).length = ∑ t ∈ Finset.univ.erase jf, (csL t).length :=
          Finset.sum_congr rfl fun t ht => by
            dsimp only [csL1]; rw [Function.update_of_ne (Finset.mem_erase.mp ht).1]
        omega
      have hsum_phi : (∑ t : Fin k, lsfPhi (x.winHandle ec t) (wc1 t) s5.mem) +
            lsfPhi (x.winHandle ec jf) (x.winConc ec jf) s.mem =
          (∑ t : Fin k, lsfPhi (x.winHandle ec t) (wc t) s.mem) +
            lsfPhi (x.winHandle ec jf) xB stB.mem := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jf),
          ← Finset.add_sum_erase _ (fun t => lsfPhi (x.winHandle ec t) (wc t) s.mem) (Finset.mem_univ jf)]
        have hwc_j : wc jf = x.winConc ec jf := (hrest jf (by dsimp [jf]; omega)).1
        have hwc1_j : wc1 jf = xB := Function.update_self jf xB wc
        have hrest_eq : ∑ t ∈ Finset.univ.erase jf, lsfPhi (x.winHandle ec t) (wc1 t) s5.mem =
            ∑ t ∈ Finset.univ.erase jf, lsfPhi (x.winHandle ec t) (wc t) s.mem := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have hne : t ≠ jf := (Finset.mem_erase.mp ht).1
          dsimp only [wc1]; rw [Function.update_of_ne hne]
          refine lsfPhi_congr fun a ha1 ha2 => ?_
          have hsame_t : SameStaticConcrete (x.winConc ec t) (wc t) := by
            by_cases htl : t.1 < j
            · exact (hdone t htl).1
            · rw [(hrest t (by omega)).1]; exact SameStaticConcrete.refl _
          have ha0 : (LSFRep W.h).foot (x.winHandle ec t) (x.winConc ec t) a := by
            dsimp [LSFRep]; rw [← hsame_t.endAddr]; exact ⟨ha1, ha2⟩
          have hdj := hDisj_ec t jf hne a ha0
          have ha_out : a < x.winHandle ec jf ∨ (x.winConc ec jf).endAddr (x.winHandle ec jf) ≤ a := by
            dsimp [LSFRep] at hdj; omega
          have ha_le : a < x.endAddr := lt_of_lt_of_le ha0.2 (hWins_ec t).2.2.2.2.2.2
          exact hfr_step a ha_out (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        rw [hwc_j, hwc1_j, hrest_eq]; dsimp only [s5, s4]; omega
      have hLw_eq : xP.L_w = x.L_w := hsP.2.2.2.2.2.2.2.2.1.trans hLwj
      rw [hLw_eq] at hcB
      refine ⟨stL, 3 + (cP + cB + 33) + cL + 1, wc', csL',
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s5, cP + cB + 33, cL, hcond, by decide, hbody, hrL, by simp [Expr.size]⟩)),
        hrL2, hrL3, hdoneL, hfrL, ?_⟩
      have hmul : (rem + 1) * (lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + 850) =
          rem * (lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + 850) +
          (lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + 850) := by ring
      omega
  -- Instantiate loop at `j = 0`, then zero `[bufPtr, bufPtr + 1 + len)` and return 0
  obtain ⟨stL, cL, wc', csL', hrL, hrL2, hrL3, hdoneL, hfrL, hcL⟩ :=
    hloop k 0 st9 (fun t => x.winConc ec t) (fun _ => []) (Nat.zero_le k) (by omega)
      (by simp [st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState])
      (by simp [st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState])
      (by simp [st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState])
      (by simp [st9, st8, st7, st6, st5, st4, st3, st2, st1])
      (by simp [st9, st8, st7, st6, st5, st4, st3, st2])
      (by simp [st9, st8, st7, st6, st5, st4])
      (by simp [st9, st8, st7, st6, st5])
      (by simp [st9, st8, st7, st6])
      (by simp [st9, st8, st7])
      (by simp [st9, st8])
      (by simp [st9])
      (fun _ h => by omega) (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ _ => rfl)
  obtain ⟨bodyZ, hbodyZ, oZ, stZ, cZ, hrZ, ⟨pZ, lZ, hargZ, hoZ, hZ_post, hZ_fr⟩, hZ_cost⟩ :=
    compZeroRange_meetsContract hpZero [bufPtr, 1 + len] stL.mem stL.pos ω
      (by simp; omega) ⟨bufPtr, 1 + len, rfl, hw16, by omega⟩
  have hbpZ : bodyZ = compZeroRangeProc := Option.some.inj (hbodyZ.symm.trans hpZero)
  have ⟨hpZ, hlZ⟩ : pZ = bufPtr ∧ lZ = 1 + len := by simpa [eq_comm] using hargZ
  rw [hpZ, hlZ] at hZ_post hZ_fr
  subst hbpZ
  let stCallZ : State := { mem := stZ.mem, regs := Function.update stL.regs 16 0, pos := stZ.pos }
  have hcallZ : Runs w p ω (.call 16 bZero [.reg 2, .reg 3]) stL .normal stCallZ (2 + cZ + 1) :=
    runs_call_iff.mpr ⟨[bufPtr, 1 + len], compZeroRangeProc, oZ, stZ, cZ,
      by simp [evalArgs, Expr.eval, hrL2, hrL3], hpZero, hrZ, rfl, by simp [stCallZ, hoZ], by simp [argsSize, Expr.size]⟩
  have hret : Runs w p ω (.ret (.const 0)) stCallZ (.returned 0) stCallZ 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  have hfull : Runs w p ω (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)) st0 (.returned 0)
      stCallZ (cL + cZ + 57) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 5, cL + cZ + 51, hp1,
    runs_seq_iff.mpr (Or.inr ⟨st2, 5, cL + cZ + 45, hp2,
    runs_seq_iff.mpr (Or.inr ⟨st3, 5, cL + cZ + 39, hp3,
    runs_seq_iff.mpr (Or.inr ⟨st4, 6, cL + cZ + 32, hp4,
    runs_seq_iff.mpr (Or.inr ⟨st5, 4, cL + cZ + 27, hp5,
    runs_seq_iff.mpr (Or.inr ⟨st6, 4, cL + cZ + 22, hp6,
    runs_seq_iff.mpr (Or.inr ⟨st7, 6, cL + cZ + 15, hp7,
    runs_seq_iff.mpr (Or.inr ⟨st8, 4, cL + cZ + 10, hp8,
    runs_seq_iff.mpr (Or.inr ⟨st9, 2, cL + cZ + 7, hp9,
    runs_seq_iff.mpr (Or.inr ⟨stL, cL, cZ + 6, hrL,
    runs_seq_iff.mpr (Or.inr ⟨stCallZ, 2 + cZ + 1, 2, hcallZ, hret, by omega⟩), by omega⟩),
      by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  have hcutsL_le : ∀ t : Fin k, cnts t + (csL' t).length ≤ x.vCap := by
    intro t
    have h1 := hcap t
    have hct := (List.toFinset_card_of_nodup (hdoneL t).2.2.2.2.2.2.2.2.1).symm
    rw [List.length_map] at hct
    have hsub : ((csL' t).map Prod.snd).toFinset ⊆
        ((applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) u_c).R_orig \
          ((S t).compSt (x.compOf (x.edgefulComp ec))).R_orig) := by
      intro z hz; have h2 := (hdoneL t).2.2.2.2.2.2.2.2.2
      cases u_c with
      | split v v' St Sh =>
        rw [h2.2.2] at hz; rw [Finset.mem_sdiff, Finset.mem_erase] at hz
        have hiso : (applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) (.split v v' St Sh)).isolatedVerts =
            insert v' ((S t).compSt (x.compOf (x.edgefulComp ec))).isolatedVerts := rfl
        simp only [LSFState.RF, LSFState.R, hiso, Finset.mem_union, Finset.mem_insert] at hz
        exact Finset.mem_sdiff.mpr ⟨by tauto, fun h => hz.2 (Or.inl h)⟩
      | insert e a b_v =>
        rw [h2] at hz; rw [Finset.mem_sdiff] at hz
        have hiso : (applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) (.insert e a b_v)).isolatedVerts =
            ((S t).compSt (x.compOf (x.edgefulComp ec))).isolatedVerts := rfl
        simp only [LSFState.RF, LSFState.R, hiso, Finset.mem_union] at hz
        exact Finset.mem_sdiff.mpr ⟨by tauto, fun h => hz.2 (Or.inl h)⟩
      | delete e =>
        rw [h2] at hz; rw [Finset.mem_sdiff] at hz
        have hiso : (applyLSFUpdate ((S t).compSt (x.compOf (x.edgefulComp ec))) (.delete e)).isolatedVerts =
            ((S t).compSt (x.compOf (x.edgefulComp ec))).isolatedVerts := rfl
        simp only [LSFState.RF, LSFState.R, hiso, Finset.mem_union] at hz
        exact Finset.mem_sdiff.mpr ⟨by tauto, fun h => hz.2 (Or.inl h)⟩
    have := Finset.card_le_card hsub; omega
  have hZ_out : ∀ a, a < bufPtr ∨ bufPtr + (1 + len) ≤ a → stZ.mem a = stL.mem a := hZ_fr
  have hphi_Z : ∑ t : Fin k, lsfPhi (x.winHandle ec t) (wc' t) stCallZ.mem =
      ∑ t : Fin k, lsfPhi (x.winHandle ec t) (wc' t) stL.mem :=
    Finset.sum_congr rfl fun t _ => lsfPhi_congr fun a _ ha2 =>
      hZ_out a (Or.inl (by
        have := (hdoneL t).1.endAddr (x.winHandle ec t)
        have := (hWins_ec t).2.2.2.2.2.2; omega))
  refine ⟨stCallZ, cL + cZ + 57, wc', csL', hfull, ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨hs_t, hrep_t, hcnt_t, hlog_t, hv_t, hf_t, hndE_t, hsE_t, hndR_t, hsR_t⟩ := hdoneL t
    have ht_le : (t.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
    have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
    have hcl_t := hcutsL_le t
    have hrep_tZ : (LSFRep W.h).rep (x.winHandle ec t) _ (wc' t) stCallZ.mem :=
      (lsfRep_local W.h _ _ _ stL.mem stCallZ.mem fun a ha =>
        (hZ_out a (Or.inl (by have := hs_t.endAddr (x.winHandle ec t); have := (hWins_ec t).2.2.2.2.2.2; have := ha.2; omega))).symm).1 hrep_t
    exact ⟨hs_t, hrep_tZ, (hZ_out _ (Or.inl (by have := t.2; omega))).trans hcnt_t,
      fun i hi => ⟨(hZ_out _ (Or.inl (by omega))).trans (hlog_t i hi).1,
        (hZ_out _ (Or.inl (by omega))).trans (hlog_t i hi).2⟩,
      hv_t, hf_t, hndE_t, hsE_t, hndR_t, by cases u_c <;> exact hsR_t⟩
  · intro a h1 h2 h3 h4 h5
    exact (hZ_out a h5).trans (hfrL a h1 h2 h3 h4)
  · intro a ha
    by_cases hlt : a < bufPtr + (1 + len)
    · have := hZ_post (a - bufPtr) (by omega)
      rwa [show bufPtr + (a - bufPtr) = a by omega] at this
    · refine (hZ_out a (Or.inr (by omega))).trans ((hfrL a
        (fun t hft => by have := (hWins_ec t).2.2.2.2.2.2; have := hft.2; omega)
        (fun t => by have := t.2; omega)
        (fun t => Or.inr (by
          have := hcutsL_le t
          have ht_le : (t.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
          have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
          omega))
        (fun t => Or.inr (by
          have := hcutsL_le t
          have ht_le : (t.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by omega)
          have ht_eq : (t.1 + 1) * x.vCap = t.1 * x.vCap + x.vCap := by ring
          omega))).trans (hz a (by omega)))
  · have hZ_c : cZ ≤ 20 * (1 + len) + 15 := by simpa [compZeroRangeContract] using hZ_cost
    rw [hphi_Z]
    have hmem9 : st9.mem = mem := rfl
    rw [hmem9] at hcL
    simp only [List.length_nil, Finset.sum_const_zero, mul_zero, add_zero] at hcL
    omega

end

end MinCostFlow.SparseCore.Program
