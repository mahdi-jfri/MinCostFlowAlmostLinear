module

public import MinCostFlow.SparseCore.Program.CompBatchStepInsSame
public import MinCostFlow.SparseCore.Program.CompBatchStepInsCross
import WordRAM.Tactic

/-!
# Edge-Insertion Step Entry Point (`CompBatchStepIns`)

Assembles `compStepInsert_runs` for `compStepInsertProc` from `compStepInsPref_runs`,
`compStepInsSame_runs`, and `compStepInsCross_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

open Classical in
/-- Verification of `compStepInsertProc`: processes an encoded `.insert e a bVert` at `uPtr` and
returns `uPtr + 4`, maintaining `CompLSFRepDirty`, cut logs, `ZeroFrom`, frame, and uniform
amortized cost `≤ 600 + k * ∑_{touched edgeful} (...)`. -/
theorem compStepInsert_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bCons bMark bDisp uPtr heap cntBase updBuf e a bVert : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {touched : List ℕ} {cnts : Fin k → ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpCons : p.procs[bCons]? = some ghostConsProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (htouch_nd : touched.Nodup)
    (htouch_lt : ∀ c ∈ touched, c < x.numComps)
    (hu_in : mem uPtr = 0 ∧ mem (uPtr + 1) = e ∧ mem (uPtr + 2) = a ∧ mem (uPtr + 3) = bVert)
    (hu_valid : (S ⟨0, hrep.1⟩).G.UpdateIsValid (.insert e a bVert))
    (heCap : e < x.eCap)
    (hend_heap : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + touched.length + 2 ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hbuf_w : updBuf + 5 < 2 ^ w)
    (hu_w : uPtr + 4 < 2 ^ w)
    (hz : ZeroFrom mem updBuf)
    (hcnt_touch : mem heap = touched.length)
    (hlist_touch : ListAt mem (heap + 1) touched)
    (hcnts_m : ∀ j : Fin k, mem (cntBase + j.1) = cnts j)
    (hcnts_le : ∀ j : Fin k, cnts j ≤ (S j).RF.R.card) :
    let cs0 := S ⟨0, hrep.1⟩
    let S' : CompLSFFamily k := fun j => compLSFStepSingle (S j) (.insert e a bVert)
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (x' : CompLSFMeta k) (touched' : List ℕ) (cuts : Fin k → List (ℕ × ℕ)),
      Runs w p ω (compStepInsertProc bCons bMark bDisp)
        (startState [b, uPtr, heap, cntBase, updBuf] mem pos) (.returned (uPtr + 4)) st' cost ∧
      x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.L_w = x.L_w ∧
      x'.numComps = x.numComps ∧ x'.numEdgeful = x.numEdgeful ∧
      x'.m0Total = x.m0Total ∧ x'.endAddr = x.endAddr ∧ HEq x'.compOf x.compOf ∧
      CompLSFRepDirty W k b S' x' touched' st'.mem ∧
      touched'.Nodup ∧ (∀ c ∈ touched', c < x.numComps) ∧
      touched'.length ≤ touched.length + 2 ∧
      (∀ c : Fin x.numComps, c.1 ∈ touched' ↔
        c.1 ∈ touched ∨ x.compOf c ∈ touchedComps cs0 (.insert e a bVert)) ∧
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
        k * ((touchedComps cs0 (.insert e a bVert)).filter fun C =>
              1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
          lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.insert e a bVert)) * x.L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.insert e a bVert) * x.L_w)) := by
  intro cs0 S' rootsBase fDelBase
  have ⟨hk, _, _, _, _, _, _, _, _, hTE, hhdr, ⟨ℓ₀, hBr⟩, _, hT, _, _, hVComp, _, _, _, _, _, _, _⟩ := hrep
  have hI0 : CompLSFInv W.C_lsst ℓ₀ cs0 := (hBr ⟨0, hk⟩).1
  obtain ⟨C1, hC1, haC1⟩ := Finset.mem_biUnion.mp (hI0.hV_eq ▸ hu_valid.2.1)
  obtain ⟨c1, rfl⟩ := (hT.hBij.2 C1).mp hC1
  obtain ⟨C2, hC2, hbC2⟩ := Finset.mem_biUnion.mp (hI0.hV_eq ▸ hu_valid.2.2)
  obtain ⟨c2, rfl⟩ := (hT.hBij.2 C2).mp hC2
  obtain ⟨cP, hrunP, hcP⟩ := compStepInsPref_runs (p := p) (b := b) (uPtr := uPtr) (heap := heap)
    (cntBase := cntBase) (updBuf := updBuf) (pos := pos) (ω := ω) hw16 hTE (by omega) (by omega) hu_w hhdr
    ⟨hu_in.2.1, hu_in.2.2.1, hu_in.2.2.2⟩ heCap (hT.hVlt a hu_valid.2.1) (hT.hVlt bVert hu_valid.2.2)
    (hVComp c1 a haC1) (hVComp c2 bVert hbC2)
  set st0 := startState [b, uPtr, heap, cntBase, updBuf] mem pos
  set m3 := Function.update (Function.update (Function.update mem
    (compEdgeC1Base b x.vCap + e) c1.1) (compEdgeC2Base b x.vCap x.eCap + e) c2.1)
    (compIsInsBase b x.vCap x.eCap + e) 1
  set regsP :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
      st0.regs 5 e) 6 a) 7 bVert) 8 x.vCap) 9 x.eCap) 10 (compVCompBase b))
      11 c1.1) 12 c2.1) 13 (compEdgeC1Base b x.vCap)) 14 (compEdgeC2Base b x.vCap x.eCap))
      15 (compIsInsBase b x.vCap x.eCap)) 16 (compTouchMarkBase b x.vCap x.eCap))
      17 (heap + 1)) 18 (compEdgefulBase b x.vCap)) 19 (compEdgefulIdxBase b x.vCap)
  set stP : State := { st0 with regs := regsP, mem := m3 }
  have hw4 : 4 < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  by_cases h12 : c1 = c2
  · subst h12
    obtain ⟨st', cB, x', touched', cuts, hrunB, hr1, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', hcost'⟩ :=
      compStepInsSame_runs (uPtr := uPtr) (ω := ω) hpZero hpLogAdd hpPreLog hpLsf hpMark hpDisp hw16 hrep htouch_nd htouch_lt
        hu_valid heCap c1 haC1 hbC2 hend_heap hheap_cnt hcnt_buf hbuf_w hz hcnt_touch hlist_touch
        hcnts_m hcnts_le (stP := stP) (by simp [stP, regsP, st0, startState]) rfl
    have hrun_cond : Runs w p ω (.cond (.bin .eq (.reg 11) (.reg 12))
        (compStepInsSameStmt bMark bDisp) (compStepInsCrossStmt bCons bMark bDisp)) stP .normal st' (cB + 4) := by
      rw [runs_cond_iff]
      refine ⟨1, cB, by simp [Expr.eval, BinOp.eval, stP, regsP, hw0], ?_, by simp [Expr.size]; omega⟩
      simpa using hrunB
    have hrun_ret : Runs w p ω (.ret (.bin .add (.reg 1) (.const 4))) st' (.returned (uPtr + 4)) st' 4 := by
      rw [runs_ret_iff]
      exact ⟨uPtr + 4, by simp [Expr.eval, BinOp.eval, hr1, hw4, hu_w], rfl, rfl, by simp [Expr.size]⟩
    have hrun_full : Runs w p ω (compStepInsertProc bCons bMark bDisp) st0 (.returned (uPtr + 4)) st' (cP + cB + 10) :=
      runs_seq_iff.mpr (Or.inr ⟨stP, cP, _, hrunP,
        runs_seq_iff.mpr (Or.inr ⟨st', cB + 4, 4, hrun_cond, hrun_ret, rfl⟩), by omega⟩)
    exact ⟨st', cP + cB + 10, x', touched', cuts, hrun_full, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', by linarith⟩
  · obtain ⟨st', cB, x', touched', cuts, hrunB, hr1, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', hcost'⟩ :=
      compStepInsCross_runs (uPtr := uPtr) (ω := ω) hpZero hpLogAdd hpPreLog hpLsf hpCons hpMark hpDisp hw16 hrep htouch_nd htouch_lt
        hu_valid heCap c1 c2 h12 haC1 hbC2 hend_heap hheap_cnt hcnt_buf hbuf_w hz hcnt_touch hlist_touch
        hcnts_m hcnts_le (stP := stP) (by simp [stP, regsP, st0, startState]) rfl
    have h12_val : c1.1 ≠ c2.1 := fun h => h12 (Fin.ext h)
    have hrun_cond : Runs w p ω (.cond (.bin .eq (.reg 11) (.reg 12))
        (compStepInsSameStmt bMark bDisp) (compStepInsCrossStmt bCons bMark bDisp)) stP .normal st' (cB + 4) := by
      rw [runs_cond_iff]
      refine ⟨0, cB, by simp [Expr.eval, BinOp.eval, stP, regsP, h12_val, hw0], ?_, by simp [Expr.size]; omega⟩
      simpa using hrunB
    have hrun_ret : Runs w p ω (.ret (.bin .add (.reg 1) (.const 4))) st' (.returned (uPtr + 4)) st' 4 := by
      rw [runs_ret_iff]
      exact ⟨uPtr + 4, by simp [Expr.eval, BinOp.eval, hr1, hw4, hu_w], rfl, rfl, by simp [Expr.size]⟩
    have hrun_full : Runs w p ω (compStepInsertProc bCons bMark bDisp) st0 (.returned (uPtr + 4)) st' (cP + cB + 10) :=
      runs_seq_iff.mpr (Or.inr ⟨stP, cP, _, hrunP,
        runs_seq_iff.mpr (Or.inr ⟨st', cB + 4, 4, hrun_cond, hrun_ret, rfl⟩), by omega⟩)
    exact ⟨st', cP + cB + 10, x', touched', cuts, hrun_full, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hrep', hnd', hlt', hlen', hiff', hhp', hls', hbr', hfr', hz', by linarith⟩

end

end MinCostFlow.SparseCore.Program
