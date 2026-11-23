module

public import MinCostFlow.SparseCore.Program.CompBatchStepInsBase
import WordRAM.Tactic

/-!
# Edge-Insertion Step: Same-Component Branch (`CompBatchStepInsSame`)

Verifies `compStepInsSameStmt` for an encoded `.insert e a bVert` when both endpoints lie in the
same connected component `c1 = c2`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compStepInsSameStmt` starting from the post-prefix state `stP` when `c1 = c2`. -/
theorem compStepInsSame_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bMark bDisp uPtr heap cntBase updBuf e a bVert : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {touched : List ℕ} {cnts : Fin k → ℕ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (htouch_nd : touched.Nodup)
    (htouch_lt : ∀ c ∈ touched, c < x.numComps)
    (hu_valid : (S ⟨0, hrep.1⟩).G.UpdateIsValid (.insert e a bVert))
    (heCap : e < x.eCap)
    (c1 : Fin x.numComps)
    (haC1 : a ∈ ((S ⟨0, hrep.1⟩).compSt (x.compOf c1)).G.V)
    (hbC1 : bVert ∈ ((S ⟨0, hrep.1⟩).compSt (x.compOf c1)).G.V)
    (hend_heap : x.endAddr ≤ heap)
    (hheap_cnt : heap + 1 + touched.length + 2 ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hbuf_w : updBuf + 5 < 2 ^ w)
    (hz : ZeroFrom mem updBuf)
    (hcnt_touch : mem heap = touched.length)
    (hlist_touch : ListAt mem (heap + 1) touched)
    (hcnts_m : ∀ j : Fin k, mem (cntBase + j.1) = cnts j)
    (hcnts_le : ∀ j : Fin k, cnts j ≤ (S j).RF.R.card)
    {stP : State}
    (hstP_regs : stP.regs 0 = b ∧ stP.regs 1 = uPtr ∧ stP.regs 2 = heap ∧ stP.regs 3 = cntBase ∧
      stP.regs 4 = updBuf ∧ stP.regs 5 = e ∧ stP.regs 6 = a ∧ stP.regs 7 = bVert ∧
      stP.regs 11 = c1.1 ∧ stP.regs 16 = compTouchMarkBase b x.vCap x.eCap ∧
      stP.regs 17 = heap + 1 ∧ stP.regs 18 = compEdgefulBase b x.vCap ∧
      stP.regs 19 = compEdgefulIdxBase b x.vCap)
    (hstP_mem : stP.mem = Function.update (Function.update (Function.update mem
      (compEdgeC1Base b x.vCap + e) c1.1) (compEdgeC2Base b x.vCap x.eCap + e) c1.1)
      (compIsInsBase b x.vCap x.eCap + e) 1) :
    let cs0 := S ⟨0, hrep.1⟩
    let S' : CompLSFFamily k := fun j => compLSFStepSingle (S j) (.insert e a bVert)
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (x' : CompLSFMeta k) (touched' : List ℕ) (cuts : Fin k → List (ℕ × ℕ)),
      Runs w p ω (compStepInsSameStmt bMark bDisp) stP .normal st' cost ∧
      st'.regs 1 = uPtr ∧
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
        compPhi b x mem + 280 +
        k * ((touchedComps cs0 (.insert e a bVert)).filter fun C =>
              1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
          lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.insert e a bVert)) * x.L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.insert e a bVert) * x.L_w)) := by
  intro cs0 S' rootsBase fDelBase
  obtain ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩,
    hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩ := hrep
  have hI0 : CompLSFInv W.C_lsst ℓ₀ cs0 := (hBr ⟨0, hk⟩).1
  have hS_G : ∀ j : Fin k, (S j).G = cs0.G := fun j => (hBr j).2.2.1
  have hC1 : x.compOf c1 ∈ components cs0.G₀ := hT.compOf_mem c1
  have ha_lt : a < x.vCap := hT.hVlt a hu_valid.2.1
  have hb_lt : bVert < x.vCap := hT.hVlt bVert hu_valid.2.2
  have ha_only : ∀ c : Fin x.numComps, a ∈ (cs0.compSt (x.compOf c)).G.V ↔ c = c1 := fun c =>
    ⟨fun h => by
      by_contra hne
      exact Finset.disjoint_left.mp (hI0.hV_disj _ (hT.compOf_mem c) _ hC1 (fun h' => hne (hT.hBij.1 h'))) h haC1,
     fun h => h ▸ haC1⟩
  have hb_only : ∀ c : Fin x.numComps, bVert ∈ (cs0.compSt (x.compOf c)).G.V ↔ c = c1 := fun c =>
    ⟨fun h => by
      by_contra hne
      exact Finset.disjoint_left.mp (hI0.hV_disj _ (hT.compOf_mem c) _ hC1 (fun h' => hne (hT.hBij.1 h'))) h hbC1,
     fun h => h ▸ hbC1⟩
  have htouch_iff : ∀ c : Fin x.numComps,
      x.compOf c ∈ touchedComps cs0 (.insert e a bVert) ↔ c = c1 := fun c => by
    have hmem : x.compOf c ∈ touchedComps cs0 (.insert e a bVert) ↔
        x.compOf c ∈ components cs0.G₀ ∧ projCompUpdateG cs0.G (cs0.compSt (x.compOf c)).G (.insert e a bVert) ≠ [] :=
      Finset.mem_filter
    rw [hmem, and_iff_right (hT.compOf_mem c)]
    dsimp only [projCompUpdateG]
    simp only [ha_only c, hb_only c]
    by_cases hc : c = c1 <;> simp [hc]
  have hefComp_inj : ∀ ec₁ ec₂ : Fin x.numEdgeful, x.edgefulComp ec₁ = x.edgefulComp ec₂ → ec₁ = ec₂ := by
    intro ec₁ ec₂ heq; have h1 := (hEfMeta ec₁).2; have h2 := (hEfMeta ec₂).2
    rw [heq] at h1; exact Fin.ext (h1.symm.trans h2)
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := by omega
  have hb_hdr_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hte_w ⊢; omega
  have htm_w : compTouchMarkBase b x.vCap x.eCap + x.vCap < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase,
      compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
      compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have htm_lt_end : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ x.endAddr := by
    have : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase,
        compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
        compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have h_iscr_w : compIsCrossBase b x.vCap x.eCap + e < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compIsCrossBase, compEdgeC2Base,
      compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
      compVCompBase, compHdrSize] at hte_w ⊢; omega
  have hmP_fr : ∀ z, z ≠ compEdgeC1Base b x.vCap + e → z ≠ compEdgeC2Base b x.vCap x.eCap + e →
      z ≠ compIsInsBase b x.vCap x.eCap + e → stP.mem z = mem z := fun z h1 h2 h3 => by
    rw [hstP_mem, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hmP_ec1 : stP.mem (compEdgeC1Base b x.vCap + e) = c1.1 := by
    rw [hstP_mem, Function.update_of_ne (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega),
        Function.update_of_ne (by dsimp only [compEdgeC2Base]; omega), Function.update_self]
  have hmP_ec2 : stP.mem (compEdgeC2Base b x.vCap x.eCap + e) = c1.1 := by
    rw [hstP_mem, Function.update_of_ne (by dsimp only [compIsInsBase, compIsCrossBase]; omega), Function.update_self]
  have hmP_ins : stP.mem (compIsInsBase b x.vCap x.eCap + e) = 1 := by rw [hstP_mem, Function.update_self]
  -- Step 1-2: write `isCross[e] := 0`
  let mC := Function.update stP.mem (compIsCrossBase b x.vCap x.eCap + e) 0
  let stC1 : State := { stP with regs := Function.update stP.regs 20 (compIsCrossBase b x.vCap x.eCap) }
  let stC2 : State := { stC1 with mem := mC }
  have hrun_c1 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr)))) stP .normal stC1 5 := by
    rw [runs_assign_iff]; refine ⟨compIsCrossBase b x.vCap x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h16 : b + compOffIsCrossPtr ≠ compEdgeC1Base b x.vCap + e ∧
        b + compOffIsCrossPtr ≠ compEdgeC2Base b x.vCap x.eCap + e ∧
        b + compOffIsCrossPtr ≠ compIsInsBase b x.vCap x.eCap + e := by
      dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
        compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compOffIsCrossPtr]
      exact ⟨by omega, by omega, by omega⟩
    have hw16' : 16 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
    have hb16_w : b + 16 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
    have hstP_16 : stP.mem (b + 16) = compIsCrossBase b x.vCap x.eCap := by
      have h16' := hmP_fr (b + 16) h16.1 h16.2.1 h16.2.2
      exact h16'.trans (by simpa [compOffIsCrossPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    simp [Expr.eval, BinOp.eval, hstP_regs.1, compOffIsCrossPtr, hw16', hb16_w, hstP_16]
  have hrun_c2 : Runs w p ω (.store (.bin .add (.reg 20) (.reg 5)) (.const 0)) stC1 .normal stC2 5 := by
    rw [runs_store_iff]; refine ⟨compIsCrossBase b x.vCap x.eCap + e, 0, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
    · simp [Expr.eval, BinOp.eval, stC1, hstP_regs.2.2.2.2.2.1, h_iscr_w]
    · simp [Expr.eval]
  have hmC_ge_tm : ∀ z, compTouchMarkBase b x.vCap x.eCap ≤ z → mC z = mem z := fun z hz' => by
    dsimp only [mC]
    rw [Function.update_of_ne (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase] at hz' ⊢; omega)]
    exact hmP_fr z
      (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base] at hz' ⊢; omega)
      (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase] at hz' ⊢; omega)
      (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase] at hz' ⊢; omega)
  have hmC_lt_ec1 : ∀ z < compEdgeC1Base b x.vCap, mC z = mem z := fun z hz' => by
    dsimp only [mC]
    rw [Function.update_of_ne (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega)]
    exact hmP_fr z (by omega) (by dsimp only [compEdgeC2Base]; omega)
      (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega)
  have hmC_mk : mC (compTouchMarkBase b x.vCap x.eCap + c1.1) = if c1.1 ∈ touched then 1 else 0 :=
    (hmC_ge_tm _ (Nat.le_add_right _ _)).trans (hTM c1.1 (by have := c1.2; omega))
  -- Step 3: call `compMarkTouchProc`
  obtain ⟨oM, stM, cM, hrunM, _, hmkM, hcntM, hlistM, hfrM, hcM⟩ :=
    compMarkTouch_call (cap := x.vCap) (c := c1.1) (L := touched) (pos := stC2.pos) (ω := ω)
      hpMark hw16 (by have := c1.2; omega) htm_w
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun i hi => ⟨by omega, by omega⟩)
      ((hmC_ge_tm heap (by omega)).trans hcnt_touch)
      (fun i hi => (hmC_ge_tm (heap + 1 + i) (by omega)).trans (hlist_touch i hi))
      (by rw [hmC_mk]; split_ifs <;> simp)
  set touched' := if mC (compTouchMarkBase b x.vCap x.eCap + c1.1) = 0 then touched ++ [c1.1] else touched
  let stC3 : State := { stC2 with regs := Function.update stC2.regs 20 oM.value, mem := stM.mem, pos := stM.pos }
  have hrun_m : Runs w p ω (.call 20 bMark [.reg 16, .reg 17, .reg 2, .reg 11]) stC2 .normal stC3 (cM + 5) := by
    rw [runs_call_iff]
    refine ⟨[compTouchMarkBase b x.vCap x.eCap, heap + 1, heap, c1.1], compMarkTouchProc,
      oM, stM, cM, ?_, hpMark, hrunM, rfl, rfl, by simp [Expr.size]; omega⟩
    simp [evalArgs, Expr.eval, stC2, stC1, hstP_regs.2.2.1, hstP_regs.2.2.2.2.2.2.2.2.1,
      hstP_regs.2.2.2.2.2.2.2.2.2.1, hstP_regs.2.2.2.2.2.2.2.2.2.2.1]
  have hM_below_tm : ∀ z < compTouchMarkBase b x.vCap x.eCap, stM.mem z = mC z := fun z hz' =>
    hfrM z (by omega) (by omega) (by omega)
  have hM_below_ec1 : ∀ z < compEdgeC1Base b x.vCap, stM.mem z = mem z := fun z hz' =>
    (hM_below_tm z (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega)).trans (hmC_lt_ec1 z hz')
  have hM_ge_handles : ∀ z, compHandlesBase b x.vCap x.eCap x.L_w ≤ z → z < heap → stM.mem z = mem z := fun z h1 h2 => by
    have hge_tm : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ z := by
      dsimp only [compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize,
        compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at h1 ⊢; omega
    exact (hfrM z (by have := c1.2; omega) (by omega) (by omega)).trans (hmC_ge_tm z (by omega))
  have hM_ge_cnt : ∀ z, cntBase ≤ z → stM.mem z = mem z := fun z hz' =>
    (hfrM z (by omega) (by omega) (by omega)).trans (hmC_ge_tm z (by omega))
  -- Step 4: dispatch `(c1, a, bVert)`
  have hM_ef_spec : 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m →
      ∃ ec : Fin x.numEdgeful, x.edgefulIdx c1 = ec.1 ∧
        stM.mem (compEdgefulIdxBase b x.vCap + c1.1) = ec.1 ∧ x.edgefulComp ec = c1 ∧
        CompDispatchWinOk W k b S x ec stM.mem := by
    intro hpos
    obtain ⟨ec, hidx, hmem_idx, hcomp⟩ := (hCompMeta c1).2.2.2 hpos
    have hmi : stM.mem (compEdgefulIdxBase b x.vCap + c1.1) = ec.1 :=
      (hM_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; have := c1.2; omega)).trans hmem_idx
    have hwin_orig : CompDispatchWinOk W k b S x ec mem :=
      ⟨hk, hLw, hnumEf, hTE, hhdr.2.2.1, hhdr.1, hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
       fun j => (hBr j).2.2.2.2.2.2 (x.edgefulComp ec), fun j => hWins ec j,
       fun j₁ j₂ hne => hDisj ec ec j₁ j₂ (Or.inr hne)⟩
    refine ⟨ec, hidx, hmi, hcomp, hwin_orig.of_agree
      ⟨hM_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compOffK]; omega),
       hM_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compOffVCap]; omega),
       hM_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compOffHandlesPtr]; omega)⟩
      (fun j => hM_ge_handles _ (Nat.le_add_right _ _) (by
        have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        dsimp only [compTablesEnd] at hTE; omega))
      (fun j z hz => by
        obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
        have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
          dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz.1)
        exact hM_ge_handles z hge_h (lt_of_lt_of_le hz.2 (le_trans hle hend_heap)))⟩
  have hu_c1_val : (cs0.compSt (x.compOf c1)).G.UpdateIsValid (.insert e a bVert) :=
    ⟨fun h => hu_valid.1 (hI0.hCE_sub _ hC1 h), haC1, hbC1⟩
  obtain ⟨stD, cD, cuts, winConc', hrunD, hregsD, hbrD, hwinD, hfrD, hzD, hcostD⟩ :=
    compStepInsDisp_runs (rC := 11) (rA := 6) (rB := 7) (cnts := cnts) (st := stC3) (ω := ω)
      hpZero hpLogAdd hpPreLog hpLsf hpDisp hw16 hk hLw (by omega) (by omega) (by omega) c1
      hefComp_inj (fun ec => (hEfMeta ec).1)
      (by simp [stC3, stC2, stC1, hstP_regs.1])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.1])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.2.1])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.2.2.1])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.2.2.2.2.2.2.2.2.1])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.2.2.2.2.2.1])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.2.2.2.1])
      (by simp [stC3, stC2, stC1, hstP_regs.2.2.2.2.2.2.2.1])
      hnumC (by omega) hcnt_buf hbuf_w
      (fun z hz' => (hM_ge_cnt z (by omega)).trans (hz z hz'))
      (fun j => (hM_ge_cnt _ (Nat.le_add_right _ _)).trans (hcnts_m j))
      hTE
      ((hM_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; have := c1.2; omega)).trans (hCompMeta c1).1)
      hM_ef_spec
      (fun j => by
        have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
        exact compRootCap_le_vCap (hBr j).1 hTj (hcnts_le j) c1 (.insert e a bVert))
      hu_c1_val heCap ha_lt hb_lt
  have hrun_all : Runs w p ω (compStepInsSameStmt bMark bDisp) stP .normal stD (18 + cM + cD) :=
    runs_seq_iff.mpr (Or.inr ⟨stC1, 5, _, hrun_c1,
      runs_seq_iff.mpr (Or.inr ⟨stC2, 5, _, hrun_c2,
        runs_seq_iff.mpr (Or.inr ⟨stC3, cM + 5, cD, hrun_m, hrunD, rfl⟩), rfl⟩), by omega⟩)
  -- Post-step invariants
  have hBr' : ∀ j : Fin k,
      CompLSFInv W.C_lsst ℓ₀ (S' j) ∧ (S' j).G₀ = (S' ⟨0, hk⟩).G₀ ∧
      (S' j).G = (S' ⟨0, hk⟩).G ∧ (S' j).k = k ∧
      (S' j).crossEdges = (S' ⟨0, hk⟩).crossEdges ∧
      (S' j).insertedGlobal = (S' ⟨0, hk⟩).insertedGlobal ∧
      (∀ c : Fin x.numComps, ((S' j).compSt (x.compOf c)).G = ((S' ⟨0, hk⟩).compSt (x.compOf c)).G) := by
    intro j
    have hIj := (hBr j).1; have hu_j := (hS_G j).symm ▸ hu_valid; have hG0j := (hBr j).2.1
    refine ⟨compLSFInv_step hIj hu_j, hG0j, by simp [S', compLSFStepSingle, hS_G j, cs0],
      (hBr j).2.2.2.1, ?_, by simp [S', compLSFStepSingle, (hBr j).2.2.2.2.2.1], ?_⟩
    · dsimp only [S', compLSFStepSingle]
      have hex_j : ∃ C ∈ components (S j).G₀, a ∈ ((S j).compSt C).G.V ∧ bVert ∈ ((S j).compSt C).G.V :=
        ⟨x.compOf c1, hG0j.symm ▸ hC1, ((hBr j).2.2.2.2.2.2 c1).symm ▸ haC1, ((hBr j).2.2.2.2.2.2 c1).symm ▸ hbC1⟩
      have hex_0 : ∃ C ∈ components cs0.G₀, a ∈ (cs0.compSt C).G.V ∧ bVert ∈ (cs0.compSt C).G.V :=
        ⟨x.compOf c1, hC1, haC1, hbC1⟩
      rw [ite_eq_left hex_j, ite_eq_left hex_0]; exact (hBr j).2.2.2.2.1
    · intro c
      have hG_c := applyLSFBatch_G_of_valid (hIj.hCompLSF _ (hG0j.symm ▸ hT.compOf_mem c)).1
        (projCompUpdateG_valid hIj hu_j (hG0j.symm ▸ hT.compOf_mem c))
      have hG_0 := applyLSFBatch_G_of_valid (hI0.hCompLSF _ (hT.compOf_mem c)).1
        (projCompUpdateG_valid hI0 hu_valid (hT.compOf_mem c))
      change (applyLSFBatch ((S j).compSt (x.compOf c)) _).G = (applyLSFBatch (cs0.compSt (x.compOf c)) _).G
      rw [hG_c, hG_0, hS_G j, (hBr j).2.2.2.2.2.2 c]
  have hT' := compEdgeTrack_step_insert hI0 hT hu_valid heCap haC1 hbC1
  have hcross_eq : (S' ⟨0, hk⟩).crossEdges = cs0.crossEdges := by
    dsimp only [S', compLSFStepSingle]
    exact ite_eq_left ⟨x.compOf c1, hC1, haC1, hbC1⟩
  let x' : CompLSFMeta k :=
    { x with edgeC1 := Function.update x.edgeC1 e c1.1,
             edgeC2 := Function.update x.edgeC2 e c1.1, winConc := winConc' }
  have hD_below_tables : ∀ z < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k, stD.mem z = stM.mem z := fun z hz' =>
    hfrD z (fun ec j _ ha => by obtain ⟨_, _, _, _, _, hge, _⟩ := hWins ec j; exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hz' hge)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)
  have hD_below_ec1 : ∀ z < compEdgeC1Base b x.vCap, stD.mem z = mem z := fun z hz' =>
    (hD_below_tables z (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hz' ⊢; omega)).trans (hM_below_ec1 z hz')
  have htouch'_len : touched'.length ≤ touched.length + 2 := by
    dsimp only [touched']; split_ifs <;> simp
  have hD_heap : stD.mem heap = touched'.length :=
    (hfrD heap (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle hend_heap)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans hcntM
  have hD_list : ListAt stD.mem (heap + 1) touched' := fun i hi =>
    (hfrD (heap + 1 + i) (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle (by omega))))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans (hlistM i hi)
  have htouch'_iff : ∀ c : Fin x.numComps, c.1 ∈ touched' ↔ c.1 ∈ touched ∨ c = c1 := fun c => by
    dsimp only [touched']; rw [hmC_mk]
    by_cases hc1t : c1.1 ∈ touched
    · simp only [hc1t, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]
      exact ⟨Or.inl, fun h => h.elim id (fun h' => h' ▸ hc1t)⟩
    · simp only [hc1t, ↓reduceIte, List.mem_append, List.mem_singleton]
      exact ⟨fun h => h.elim Or.inl (fun h' => Or.inr (Fin.ext h')),
        fun h => h.elim Or.inl (fun h' => Or.inr (congrArg Fin.val h'))⟩
  have htouch'_nd : touched'.Nodup := by
    dsimp only [touched']; rw [hmC_mk]
    by_cases hc1t : c1.1 ∈ touched
    · simp only [hc1t, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega]; exact htouch_nd
    · simp only [hc1t, ↓reduceIte]
      exact List.nodup_append.mpr ⟨htouch_nd, List.nodup_singleton _, fun z hz w hw heq => hc1t (List.mem_singleton.mp hw ▸ heq ▸ hz)⟩
  have htouch'_lt : ∀ c ∈ touched', c < x.numComps := fun c hc => by
    dsimp only [touched'] at hc; rw [hmC_mk] at hc
    by_cases hc1t : c1.1 ∈ touched
    · simp only [hc1t, ↓reduceIte, show (1 : ℕ) ≠ 0 by omega] at hc; exact htouch_lt c hc
    · simp only [hc1t, ↓reduceIte, List.mem_append, List.mem_singleton] at hc
      exact hc.elim (htouch_lt c) (fun h => h ▸ c1.2)
  -- Assemble `CompLSFRepDirty`
  have hrep' : CompLSFRepDirty W k b S' x' touched' stD.mem := by
    refine ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE,
      compHeaderAt_of_agree hhdr (fun z hz1 hz2 => hD_below_ec1 z (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hz2 ⊢; omega)),
      ⟨ℓ₀, hBr'⟩, hm0Tot, by simpa [x'] using hT', ?_, hEfMeta, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c; dsimp only [x']; have hc_lt : c.1 < x.numComps := c.2; obtain ⟨h1, h2, h3, h4⟩ := hCompMeta c
      refine ⟨(hD_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)).trans h1,
        (hD_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base]; omega)).trans h2,
        (hD_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base]; omega)).trans h3, fun hpos => ?_⟩
      obtain ⟨ec, he1, he2, he3⟩ := h4 hpos
      exact ⟨ec, he1, (hD_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega)).trans he2, he3⟩
    · intro c v hv; dsimp only [x']
      have hv0 : v ∈ (cs0.compSt (x.compOf c)).G.V := by
        have hG := applyLSFBatch_G_of_valid (hI0.hCompLSF _ (hT.compOf_mem c)).1
          (projCompUpdateG_valid hI0 hu_valid (hT.compOf_mem c))
        have hVc : ((S' ⟨0, hk⟩).compSt (x.compOf c)).G.V = (cs0.compSt (x.compOf c)).G.V := by
          dsimp only [S', compLSFStepSingle]; rw [hG]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
        exact hVc ▸ hv
      have hv_lt : v < x.vCap := hT.hVlt v (hI0.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c, hT.compOf_mem c, hv0⟩)
      exact (hD_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)).trans (hVComp c v hv0)
    · intro f hf; dsimp only [x']
      have hf_lt : f < x.eCap := by rcases Finset.mem_insert.mp hf with rfl | hf0; exact heCap; exact hT.hElt f hf0
      rw [hD_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          hM_below_tm _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega),
          hD_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          hM_below_tm _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase]; omega)]
      have hmC_f1 : mC (compEdgeC1Base b x.vCap + f) = stP.mem (compEdgeC1Base b x.vCap + f) :=
        Function.update_of_ne (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega) _ _
      have hmC_f2 : mC (compEdgeC2Base b x.vCap x.eCap + f) = stP.mem (compEdgeC2Base b x.vCap x.eCap + f) :=
        Function.update_of_ne (by dsimp only [compIsCrossBase]; omega) _ _
      rw [hmC_f1, hmC_f2]
      by_cases hfe : f = e
      · subst hfe; simp [hmP_ec1, hmP_ec2]
      · have hf0 : f ∈ cs0.G.E := (Finset.mem_insert.mp hf).resolve_left hfe
        rw [hmP_fr _ (by omega) (by dsimp only [compEdgeC2Base]; omega) (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega),
            hmP_fr _ (by dsimp only [compEdgeC2Base]; omega) (by omega) (by dsimp only [compIsInsBase, compIsCrossBase]; omega)]
        simp [hfe, hEdgeC f hf0]
    · intro f hf; dsimp only [x'] at hf ⊢
      rw [hD_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          hM_below_tm _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase]; omega),
          hD_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          hM_below_tm _ (by dsimp only [compTouchMarkBase, compGhostBase, compGhostSize]; omega), hcross_eq]
      change mC (compIsCrossBase b x.vCap x.eCap + f) = (if f ∈ cs0.crossEdges then 1 else 0) ∧
        mC (compIsInsBase b x.vCap x.eCap + f) = if f ∈ insert e cs0.insertedGlobal then 1 else 0
      have hmC_ins : mC (compIsInsBase b x.vCap x.eCap + f) = stP.mem (compIsInsBase b x.vCap x.eCap + f) :=
        Function.update_of_ne (by dsimp only [compIsInsBase]; omega) _ _
      by_cases hfe : f = e
      · subst hfe
        have hnc : f ∉ cs0.crossEdges := fun h => hu_valid.1 (hI0.hIns_sub (hI0.hCross_sub h))
        have hmC_cr : mC (compIsCrossBase b x.vCap x.eCap + f) = 0 := Function.update_self _ _ _
        rw [hmC_cr, hmC_ins, hmP_ins]; simp [hnc]
      · have hmC_cr : mC (compIsCrossBase b x.vCap x.eCap + f) = stP.mem (compIsCrossBase b x.vCap x.eCap + f) :=
          Function.update_of_ne (by omega) _ _
        rw [hmC_cr, hmC_ins,
            hmP_fr _ (by dsimp only [compIsCrossBase, compEdgeC2Base]; omega) (by dsimp only [compIsCrossBase]; omega) (by dsimp only [compIsInsBase]; omega),
            hmP_fr _ (by dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega) (by dsimp only [compIsInsBase, compIsCrossBase]; omega) (by omega)]
        simp [hfe, (hFlags f hf).1, (hFlags f hf).2, cs0]
    · dsimp only [x']; set gPtr := compGhostBase b x.vCap x.eCap
      have hgh_ag : ∀ z, gPtr ≤ z → z < compTouchMarkBase b x.vCap x.eCap → stD.mem z = mem z := fun z h1 h2 => by
        rw [hD_below_tables z (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at h2 ⊢; omega),
            hM_below_tm z h2]
        dsimp only [mC]
        rw [Function.update_of_ne (by dsimp only [gPtr, compGhostBase, compIsInsBase] at h1; omega)]
        exact hmP_fr z (by dsimp only [gPtr, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base] at h1; omega)
          (by dsimp only [gPtr, compGhostBase, compIsInsBase, compIsCrossBase] at h1; omega)
          (by dsimp only [gPtr, compGhostBase] at h1; omega)
      refine ⟨fun v hv => ?_, fun f _ hcr => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hGhost.1 v hv
        refine ⟨h1.of_agree
            (hgh_ag _ (by dsimp only [ghostTHeadBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTHeadBase, gPtr]; omega))
            (fun f hf => have := (hT.hGT v hv).2.1 f hf; hgh_ag _ (by dsimp only [ghostTPrevBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTPrevBase, gPtr]; omega))
            (fun f hf => have := (hT.hGT v hv).2.1 f hf; hgh_ag _ (by dsimp only [ghostTNextBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostTCntBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTCntBase, gPtr]; omega)).trans h2,
          h3.of_agree
            (hgh_ag _ (by dsimp only [ghostHHeadBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHHeadBase, gPtr]; omega))
            (fun f hf => have := (hT.hGH v hv).2.1 f hf; hgh_ag _ (by dsimp only [ghostHPrevBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHPrevBase, gPtr]; omega))
            (fun f hf => have := (hT.hGH v hv).2.1 f hf; hgh_ag _ (by dsimp only [ghostHNextBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostHCntBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHCntBase, gPtr]; omega)).trans h4⟩
      · rw [hcross_eq] at hcr
        have hf0 : f ∈ cs0.G.E := hI0.hIns_sub (hI0.hCross_sub hcr)
        have hf_lt : f < x.eCap := hT.hElt f hf0
        exact ⟨(hgh_ag _ (by dsimp only [ghostTVertBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTVertBase, gPtr]; omega)).trans (hGhost.2 f hf0 hcr).1,
          (hgh_ag _ (by dsimp only [ghostHVertBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHVertBase, gPtr]; omega)).trans (hGhost.2 f hf0 hcr).2⟩
    · intro c hc; dsimp only [x'] at hc ⊢
      rw [hD_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)]
      by_cases hcc1 : c = c1.1
      · subst hcc1; rw [hmkM, ite_eq_left ((htouch'_iff c1).mpr (Or.inr rfl))]
      · rw [hfrM _ (by omega) (by omega) (by omega), hmC_ge_tm _ (Nat.le_add_right _ _), hTM c hc]
        have hiff : c ∈ touched' ↔ c ∈ touched := by dsimp only [touched']; split_ifs <;> simp [hcc1]
        simp [hiff]
    · dsimp only [x']
      have hone_ag : ∀ i < x.L_w, stD.mem (compOneLimbBase b x.vCap x.eCap + i) = mem (compOneLimbBase b x.vCap x.eCap + i) := fun i hi => by
        have hge_tm : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ compOneLimbBase b x.vCap x.eCap + i := by dsimp only [compOneLimbBase]; omega
        have h1e := compOneLimb_end_eq b x.vCap x.eCap x.L_w
        have hlt_te : compOneLimbBase b x.vCap x.eCap + i < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
          dsimp only [compTablesEnd]; omega
        rw [hD_below_tables _ hlt_te,
            hfrM _ (by have := c1.2; omega) (by omega) (by omega), hmC_ge_tm _ (by omega)]
      exact ⟨(hone_ag 0 hLw).trans hOne.1, fun i h1 h2 => (hone_ag i h2).trans (hOne.2 i h1 h2)⟩
    · intro ec j; dsimp only [x']; have hec_lt : ec.1 < x.numEdgeful := ec.2
      obtain ⟨hslot, hrep_ec, hv, he, hL, hge, hle⟩ := hWins ec j
      have hslot' : stD.mem (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) = x.winHandle ec j := by
        have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        exact (hD_below_tables _ (by dsimp only [compTablesEnd]; omega)).trans ((hM_ge_handles _ (Nat.le_add_right _ _) (by dsimp only [compTablesEnd] at hTE; omega)).trans hslot)
      by_cases hec : x.edgefulComp ec = c1
      · obtain ⟨hss, hrep_new⟩ := (hwinD ec j).1 hec
        have hSt_eq : (S' j).compSt (x.compOf (x.edgefulComp ec)) =
            applyLSFUpdate ((S j).compSt (x.compOf c1)) (.insert e a bVert) := by
          rw [hec]
          have ha_j : a ∈ ((S j).compSt (x.compOf c1)).G.V := ((hBr j).2.2.2.2.2.2 c1).symm ▸ haC1
          have hb_j : bVert ∈ ((S j).compSt (x.compOf c1)).G.V := ((hBr j).2.2.2.2.2.2 c1).symm ▸ hbC1
          change applyLSFBatch _ (projCompUpdateG (S j).G ((S j).compSt (x.compOf c1)).G (.insert e a bVert)) = _
          simp [projCompUpdateG, ha_j, hb_j, applyLSFBatch]
        exact ⟨hslot', hSt_eq ▸ hrep_new, hss.1.trans hv, hss.2.1.trans he,
          hss.2.2.2.2.2.2.2.2.1.trans hL, hge, (hss.endAddr (x.winHandle ec j)).symm ▸ hle⟩
      · have hwc : winConc' ec j = x.winConc ec j := (hwinD ec j).2 hec
        have hSt_eq : (S' j).compSt (x.compOf (x.edgefulComp ec)) = (S j).compSt (x.compOf (x.edgefulComp ec)) := by
          have ha_not : a ∉ ((S j).compSt (x.compOf (x.edgefulComp ec))).G.V := by
            rw [(hBr j).2.2.2.2.2.2]; exact fun h => hec ((ha_only _).mp h)
          have hb_not : bVert ∉ ((S j).compSt (x.compOf (x.edgefulComp ec))).G.V := by
            rw [(hBr j).2.2.2.2.2.2]; exact fun h => hec ((hb_only _).mp h)
          change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
          simp [projCompUpdateG, ha_not, hb_not, applyLSFBatch]
        have hrep_old' : (LSFRep W.h).rep (x.winHandle ec j) ((S j).compSt (x.compOf (x.edgefulComp ec)))
            (x.winConc ec j) stD.mem := by
          refine (lsfRep_local W.h _ _ _ mem stD.mem fun z hz => ?_).1 hrep_ec
          have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
            dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz.1)
          have hz_lt_end : z < x.endAddr := lt_of_lt_of_le hz.2 hle
          symm
          exact (hfrD z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hec (h ▸ h0))) z hz ha0)
            (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
            (hM_ge_handles z hge_h (lt_of_lt_of_le hz.2 (le_trans hle hend_heap)))
        rw [hwc, hSt_eq]; exact ⟨hslot', hrep_old', hv, he, hL, hge, hle⟩
    · intro ec₁ ec₂ j₁ j₂ hne z h1 h2; dsimp only [x'] at h1 h2
      have hsame : ∀ ec j, (LSFRep W.h).foot (x.winHandle ec j) (winConc' ec j) z ↔
          (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) z := fun ec j => by
        by_cases hc : x.edgefulComp ec = c1
        · simp [LSFRep, ((hwinD ec j).1 hc).1.endAddr]
        · rw [(hwinD ec j).2 hc]
      exact hDisj ec₁ ec₂ j₁ j₂ hne z ((hsame ec₁ j₁).mp h1) ((hsame ec₂ j₂).mp h2)
  -- Cost & potential bound
  have hphi_old : compPhi b x mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem :=
    compPhi_eq_sum_dirty ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE, hhdr,
      ⟨ℓ₀, hBr⟩, hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩
  have hphi_new : compPhi b x' stD.mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem :=
    compPhi_eq_sum_dirty hrep'
  have hcost_final : (18 + cM + cD) + 120 * (∑ j : Fin k, (cuts j).length) + compPhi b x' stD.mem ≤
      compPhi b x mem + 280 +
      k * ((touchedComps cs0 (.insert e a bVert)).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
        lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.insert e a bVert)) * x.L_w + 1) +
        lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.insert e a bVert) * x.L_w)) := by
    have hfilt : (touchedComps cs0 (.insert e a bVert)).filter (fun C => 1 ≤ (compGraph cs0.G₀ C).m) =
        if 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m then {x.compOf c1} else ∅ := by
      ext C; simp only [Finset.mem_filter]
      by_cases hC : C ∈ components cs0.G₀
      · obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
        rw [htouch_iff c]; split_ifs with hp
        · simp only [Finset.mem_singleton, hT.hBij.1.eq_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hp⟩⟩
        · simp only [Finset.notMem_empty, iff_false, not_and]
          intro h; subst h; exact hp
      · have hnot : C ∉ touchedComps cs0 (.insert e a bVert) := fun h => hC (Finset.mem_filter.mp h).1
        have hne : C ≠ x.compOf c1 := fun h => hC (h ▸ hC1)
        split_ifs <;> simp [hnot, hne]
    rw [hphi_new, hphi_old, hfilt]
    by_cases hpos : 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m
    · rw [ite_eq_left hpos, Finset.sum_singleton]; rw [dite_eq_left hpos] at hcostD
      obtain ⟨ec1, hec1, hcostD'⟩ := hcostD
      have hpw : projUpdWords mem cs0 (x.compOf c1) uPtr (.insert e a bVert) = 4 := by
        dsimp only [projUpdWords]; exact ite_eq_left ⟨haC1, hbC1⟩
      rw [hpw]
      have hphi_unch : ∀ ec ≠ ec1,
          (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem) =
          (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem) := fun ec hne => by
        have hne_c : x.edgefulComp ec ≠ c1 := fun h => hne (hefComp_inj ec ec1 (h.trans hec1.symm))
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(hwinD ec j).2 hne_c]
        obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
        refine lsfPhi_congr fun z hz1 hz2 => ?_
        have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
          dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz1)
        have hz_lt_end : z < x.endAddr := lt_of_lt_of_le hz2 hle
        exact (hfrD z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hne_c (h ▸ h0))) z ⟨hz1, hz2⟩ ha0)
          (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
          (hM_ge_handles z hge_h (lt_of_lt_of_le hz2 (le_trans hle hend_heap)))
      have hphi_m_ec1 : (∑ j : Fin k, lsfPhi (x.winHandle ec1 j) (x.winConc ec1 j) stM.mem) =
          (∑ j : Fin k, lsfPhi (x.winHandle ec1 j) (x.winConc ec1 j) mem) :=
        Finset.sum_congr rfl fun j _ => by
          obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec1 j
          have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ x.winHandle ec1 j := by
            dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) hge
          exact lsfPhi_congr fun z hz1 hz2 => hM_ge_handles z (le_trans hge_h hz1) (lt_of_lt_of_le hz2 (le_trans hle hend_heap))
      rw [hphi_m_ec1] at hcostD'
      rw [← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem) (Finset.mem_univ ec1),
          ← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem) (Finset.mem_univ ec1)]
      rw [Finset.sum_congr rfl fun ec hec => hphi_unch ec (Finset.mem_erase.mp hec).1]
      have habs := compSingleDispatch_cost_le (len := 4) hk hLw (by omega)
      linarith
    · rw [ite_eq_right hpos, Finset.sum_empty]; rw [dite_eq_right hpos] at hcostD
      obtain ⟨hcD, hmD⟩ := hcostD
      have hcuts0 : ∑ j : Fin k, (cuts j).length = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [(hbrD j).2.2.2 (by dsimp only [cs0] at hpos; omega)]; rfl
      have hphi_eq : (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD.mem) =
          (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem) :=
        Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => by
          rw [(hwinD ec j).2 (fun h => hpos (h ▸ (hEfMeta ec).1))]
          obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
          have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ x.winHandle ec j := by
            dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) hge
          exact lsfPhi_congr fun z hz1 hz2 => (hmD z).trans
            (hM_ge_handles z (le_trans hge_h hz1) (lt_of_lt_of_le hz2 (le_trans hle hend_heap)))
      rw [hcuts0, hphi_eq]; omega
  -- Final assembly
  refine ⟨stD, 18 + cM + cD, x', touched', cuts, hrun_all,
    by rw [hregsD 1 (by omega)]; simp [stC3, stC2, stC1, hstP_regs.2.1],
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
    hrep', htouch'_nd, htouch'_lt, htouch'_len,
    fun c => by rw [htouch'_iff c, htouch_iff c],
    hD_heap, hD_list, ?_, ?_, hzD, hcost_final⟩
  · intro j
    have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
    have hG0j := (hBr j).2.1
    have hSelf : (S' j).compSt (x.compOf c1) = applyLSFUpdate ((S j).compSt (x.compOf c1)) (.insert e a bVert) := by
      have ha_j : a ∈ ((S j).compSt (x.compOf c1)).G.V := ((hBr j).2.2.2.2.2.2 c1).symm ▸ haC1
      have hb_j : bVert ∈ ((S j).compSt (x.compOf c1)).G.V := ((hBr j).2.2.2.2.2.2 c1).symm ▸ hbC1
      change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
      simp [projCompUpdateG, ha_j, hb_j, applyLSFBatch]
    have hOther : ∀ D ∈ components (S j).G₀, D ≠ x.compOf c1 → (S' j).compSt D = (S j).compSt D := by
      intro D hD hne
      obtain ⟨c, rfl⟩ := (hTj.hBij.2 D).mp hD
      have hnec : c ≠ c1 := fun h => hne (h ▸ rfl)
      have ha_not : a ∉ ((S j).compSt (x.compOf c)).G.V := by rw [(hBr j).2.2.2.2.2.2 c]; exact fun h => hnec ((ha_only c).mp h)
      have hb_not : bVert ∉ ((S j).compSt (x.compOf c)).G.V := by rw [(hBr j).2.2.2.2.2.2 c]; exact fun h => hnec ((hb_only c).mp h)
      change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
      simp [projCompUpdateG, ha_not, hb_not, applyLSFBatch]
    have hlift := compRF_cuts_lift_one_insDel (hBr j).1 hTj ((hS_G j).symm ▸ hu_valid) hSelf hOther
      (by rw [hSelf]; rfl)
      (fun hp => let h := (hbrD j).2.2.1 (by simpa [hG0j] using hp); ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)
      (fun hm => (hbrD j).2.2.2 (by simpa [hG0j] using hm))
    obtain ⟨hval, hndE, hsE, hEsub, hndR, hsR, hRsub⟩ := hlift
    exact ⟨(hbrD j).1, (hbrD j).2.1, hval, hndE, hsE, hEsub, hndR, hsR, hRsub,
      compStep_cnts_le_of_lift (hcnts_le j) hRsub hndR hsR⟩
  · intro z hout hnh hnl hnc hnrt hnfd hlt_buf
    have h1 : stD.mem z = stM.mem z := hfrD z (fun ec j _ ha => by
      obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
      have hb_le : b ≤ x.winHandle ec j := by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hge; omega
      rcases hout with hlt | hge'
      · exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hlt hb_le))
      · exact absurd ha.2 (not_lt.mpr (le_trans hle hge'))) hnc hnrt hnfd hlt_buf
    have hne_list : z ≠ heap + 1 + touched.length := by omega
    have hne_tm : z ≠ compTouchMarkBase b x.vCap x.eCap + c1.1 := by
      have : b ≤ compTouchMarkBase b x.vCap x.eCap + c1.1 := by
        dsimp only [compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase,
          compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase,
          compEdgefulBase, compVCompBase, compHdrSize]; omega
      rcases hout with hlt | hge' <;> omega
    rw [h1, hfrM z hne_tm hnh hne_list]
    rcases hout with hlt | hge'
    · exact hmC_lt_ec1 z (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
    · exact hmC_ge_tm z (by omega)

end

end MinCostFlow.SparseCore.Program
