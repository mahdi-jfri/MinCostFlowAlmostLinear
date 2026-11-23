module

public import MinCostFlow.SparseCore.Program.CompBatchStepDelSame
public import MinCostFlow.SparseCore.Program.CompBatchStepDelCross
import WordRAM.Tactic

/-!
# Edge-Deletion Step Entry Point (`CompBatchStepDel`)

Assembles `compStepDelete_runs` for `compStepDeleteProc` from `compStepDelPref_runs`,
`compStepDelSame_runs`, and `compStepDelCross_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

open Classical in
/-- Verification of `compStepDeleteProc`: processes an encoded `.delete e` at `uPtr` and
returns `uPtr + 2`, maintaining `CompLSFRepDirty`, cut logs, `ZeroFrom`, frame, and uniform
amortized cost `≤ 600 + k * ∑_{touched edgeful} (...)`. -/
theorem compStepDelete_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bErase bMark bDisp uPtr heap cntBase updBuf e : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {touched : List ℕ} {cnts : Fin k → ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpErase : p.procs[bErase]? = some ghostEraseProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (htouch_nd : touched.Nodup)
    (htouch_lt : ∀ c ∈ touched, c < x.numComps)
    (hu_in : mem uPtr = 1 ∧ mem (uPtr + 1) = e)
    (hu_valid : (S ⟨0, hrep.1⟩).G.UpdateIsValid (.delete e))
    (hend_heap : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + touched.length + 2 ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hbuf_w : updBuf + 3 < 2 ^ w)
    (hu_w : uPtr + 2 < 2 ^ w)
    (hz : ZeroFrom mem updBuf)
    (hcnt_touch : mem heap = touched.length)
    (hlist_touch : ListAt mem (heap + 1) touched)
    (hcnts_m : ∀ j : Fin k, mem (cntBase + j.1) = cnts j)
    (hcnts_le : ∀ j : Fin k, cnts j ≤ (S j).RF.R.card) :
    let cs0 := S ⟨0, hrep.1⟩
    let S' : CompLSFFamily k := fun j => compLSFStepSingle (S j) (.delete e)
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (x' : CompLSFMeta k) (touched' : List ℕ) (cuts : Fin k → List (ℕ × ℕ)),
      Runs w p ω (compStepDeleteProc bErase bMark bDisp)
        (startState [b, uPtr, heap, cntBase, updBuf] mem pos) (.returned (uPtr + 2)) st' cost ∧
      x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
      x'.numComps = x.numComps ∧ x'.numEdgeful = x.numEdgeful ∧
      x'.m0Total = x.m0Total ∧ x'.endAddr = x.endAddr ∧ HEq x'.compOf x.compOf ∧
      CompLSFRepDirty W k b S' x' touched' st'.mem ∧
      touched'.Nodup ∧ (∀ c ∈ touched', c < x.numComps) ∧
      touched'.length ≤ touched.length + 2 ∧
      (∀ c : Fin x.numComps, c.1 ∈ touched' ↔
        c.1 ∈ touched ∨ x.compOf c ∈ touchedComps cs0 (.delete e)) ∧
      st'.mem heap = touched'.length ∧
      ListAt st'.mem (heap + 1) touched' ∧
      (∀ j : Fin k,
        st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
        (∀ i (hi : i < (cuts j).length),
          st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
          st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
        CompForestCutsValid x.vCap (S j).RF (cuts j) ∧
        ((cuts j).map Prod.fst).Nodup ∧
        ((cuts j).map Prod.fst).toFinset = (S j).RF.F.E \ (S' j).RF.F.E ∧
        (S' j).RF.F.E ⊆ (S j).RF.F.E ∧
        ((cuts j).map Prod.snd).Nodup ∧
        ((cuts j).map Prod.snd).toFinset = (S' j).RF.R \ (S j).RF.R ∧
        (S j).RF.R ⊆ (S' j).RF.R ∧
        cnts j + (cuts j).length ≤ (S' j).RF.R.card) ∧
      (∀ a,
        (a < b ∨ x.endAddr ≤ a) →
        a ≠ heap → (a < heap + 1 + touched.length ∨ heap + 1 + touched.length + 2 ≤ a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        a < updBuf → st'.mem a = mem a) ∧
      ZeroFrom st'.mem updBuf ∧
      cost + 120 * (∑ j : Fin k, (cuts j).length) + compPhi b x' st'.mem ≤
        compPhi b x mem + 600 +
        k * ((touchedComps cs0 (.delete e)).filter fun C =>
              1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
          lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.delete e)) * x.L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.delete e) * x.L_w)) := by
  intro cs0 S' rootsBase fDelBase
  have ⟨hk, _, _, _, _, _, _, _, _, hTE, hhdr, _, _, hT, _, _, _, hEdgeC, hFlags, _, _, _, _, _⟩ := hrep
  have heCap : e < x.eCap := hT.hElt e hu_valid
  obtain ⟨c1, c2, hc1_eq, hc2_eq, _, _, he_mem, hcr_iff, _⟩ := hT.hEdge e hu_valid
  set isCr := if e ∈ cs0.crossEdges then 1 else 0
  have hec1_m : mem (compEdgeC1Base b x.vCap + e) = c1.1 := (hEdgeC e hu_valid).1.trans hc1_eq
  have hec2_m : mem (compEdgeC2Base b x.vCap x.eCap + e) = c2.1 := (hEdgeC e hu_valid).2.trans hc2_eq
  have hcr_m : mem (compIsCrossBase b x.vCap x.eCap + e) = isCr := (hFlags e heCap).1
  obtain ⟨cP, hrunP, hcP⟩ := compStepDelPref_runs (p := p) (b := b) (uPtr := uPtr) (heap := heap)
    (cntBase := cntBase) (updBuf := updBuf) (pos := pos) (ω := ω) hw16 hTE (by omega) (by omega) hu_w hhdr
    hu_in.2 heCap hec1_m hec2_m hcr_m
  set st0 := startState [b, uPtr, heap, cntBase, updBuf] mem pos
  set m2 := Function.update (Function.update mem
    (compIsCrossBase b x.vCap x.eCap + e) 0) (compIsInsBase b x.vCap x.eCap + e) 0
  set regsP :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      st0.regs 5 e) 6 x.vCap) 7 x.eCap) 8 (compEdgeC1Base b x.vCap)) 9 c1.1)
      10 (compEdgeC2Base b x.vCap x.eCap)) 11 c2.1) 12 (compIsCrossBase b x.vCap x.eCap))
      13 isCr) 14 (compIsInsBase b x.vCap x.eCap)) 15 (compTouchMarkBase b x.vCap x.eCap))
      16 (heap + 1)) 17 (compEdgefulBase b x.vCap)) 18 (compEdgefulIdxBase b x.vCap)
  set stP : State := { st0 with regs := regsP, mem := m2 }
  have hw2 : 2 < 2 ^ w := by omega
  by_cases hcr : e ∈ cs0.crossEdges
  · have hisCr1 : isCr = 1 := ite_eq_left hcr
    obtain ⟨st', cB, x', touched', cuts, hrunB, hr1, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', hcost'⟩ :=
      compStepDelCross_runs (bErase := bErase) (bMark := bMark) (bDisp := bDisp) (uPtr := uPtr) (ω := ω)
        hrep htouch_nd htouch_lt hu_valid hcr hend_heap hheap_cnt hcnt_buf
        hz hcnt_touch hlist_touch hcnts_m hcnts_le (stP := stP)
        (by simp [stP, regsP, st0, startState]) rfl
    have hrun_cond : Runs w p ω (.cond (.reg 13)
        (compStepDelCrossStmt bErase bMark bDisp) (compStepDelSameStmt bMark bDisp)) stP .normal st' (cB + 2) := by
      rw [runs_cond_iff]
      refine ⟨1, cB, by simp [Expr.eval, stP, regsP, hisCr1], ?_, by simp [Expr.size]; omega⟩
      simpa using hrunB
    have hrun_ret : Runs w p ω (.ret (.bin .add (.reg 1) (.const 2))) st' (.returned (uPtr + 2)) st' 4 := by
      rw [runs_ret_iff]
      exact ⟨uPtr + 2, by simp [Expr.eval, BinOp.eval, hr1, hw2, hu_w], rfl, rfl, by simp [Expr.size]⟩
    have hrun_full : Runs w p ω (compStepDeleteProc bErase bMark bDisp) st0 (.returned (uPtr + 2)) st' (cP + cB + 8) :=
      runs_seq_iff.mpr (Or.inr ⟨stP, cP, _, hrunP,
        runs_seq_iff.mpr (Or.inr ⟨st', cB + 2, 4, hrun_cond, hrun_ret, rfl⟩), by omega⟩)
    exact ⟨st', cP + cB + 8, x', touched', cuts, hrun_full, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', by linarith⟩
  · have h12 : c1 = c2 := by by_contra hne; exact hcr (hcr_iff.mpr hne)
    subst h12
    have hisCr0 : isCr = 0 := ite_eq_right hcr
    have he_c1 : ∀ c : Fin x.numComps, e ∈ (cs0.compSt (x.compOf c)).G.E ↔ c = c1 := fun c => by
      simpa using he_mem c
    obtain ⟨st', cB, x', touched', cuts, hrunB, hr1, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', hcost'⟩ :=
      compStepDelSame_runs (uPtr := uPtr) (ω := ω) hpZero hpLogAdd hpPreLog hpLsf hpMark hpDisp hw16
        hrep htouch_nd htouch_lt hu_valid hcr c1 he_c1 hend_heap hheap_cnt hcnt_buf hbuf_w
        hz hcnt_touch hlist_touch hcnts_m hcnts_le (stP := stP)
        (by simp [stP, regsP, st0, startState]) rfl
    have hrun_cond : Runs w p ω (.cond (.reg 13)
        (compStepDelCrossStmt bErase bMark bDisp) (compStepDelSameStmt bMark bDisp)) stP .normal st' (cB + 2) := by
      rw [runs_cond_iff]
      refine ⟨0, cB, by simp [Expr.eval, stP, regsP, hisCr0], ?_, by simp [Expr.size]; omega⟩
      simpa using hrunB
    have hrun_ret : Runs w p ω (.ret (.bin .add (.reg 1) (.const 2))) st' (.returned (uPtr + 2)) st' 4 := by
      rw [runs_ret_iff]
      exact ⟨uPtr + 2, by simp [Expr.eval, BinOp.eval, hr1, hw2, hu_w], rfl, rfl, by simp [Expr.size]⟩
    have hrun_full : Runs w p ω (compStepDeleteProc bErase bMark bDisp) st0 (.returned (uPtr + 2)) st' (cP + cB + 8) :=
      runs_seq_iff.mpr (Or.inr ⟨stP, cP, _, hrunP,
        runs_seq_iff.mpr (Or.inr ⟨st', cB + 2, 4, hrun_cond, hrun_ret, rfl⟩), by omega⟩)
    exact ⟨st', cP + cB + 8, x', touched', cuts, hrun_full, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', by linarith⟩

end

end MinCostFlow.SparseCore.Program
