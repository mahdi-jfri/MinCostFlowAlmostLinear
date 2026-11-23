module

public import MinCostFlow.SparseCore.Program.CompBatchStepInsGhost
import WordRAM.Tactic

/-!
# Edge-Insertion Step: Cross-Component Branch (`CompBatchStepInsCross`)

Verifies `compStepInsCrossStmt` (cross-component insertion `c1 ≠ c2`), with cross-inserts projected
to insert-then-delete self-loops: it calls `compStepInsCrossPre_runs` to set `isCross[e] := 1` and
mark `c1, c2` touched, then runs `compStepInsDelPairDisp_runs` on `c1`
(`[.insert e a a, .delete e]`) and `c2` (`[.insert e bVert bVert, .delete e]`), lifting both
components' forest cuts to global `cs.RF`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

private lemma compPairDispatch_cost_le {k L_w : ℕ} (hk : 1 ≤ k) (hLw : 1 ≤ L_w) :
    k * (lsfBatchCostFactor * (8 * L_w + 2) + 1700) + 600 ≤
      k * (lsfBatchCostFactor * (7 * L_w + 1) + lsfBatchCostFactor * (6 * L_w)) := by
  have h1 : 600 ≤ k * 600 := Nat.le_mul_of_pos_left 600 hk
  have hfac : lsfBatchCostFactor = 10000 := rfl
  have h2 : lsfBatchCostFactor * (8 * L_w + 2) + 1700 + 600 ≤
      lsfBatchCostFactor * (7 * L_w + 1) + lsfBatchCostFactor * (6 * L_w) := by
    rw [hfac]; omega
  calc k * (lsfBatchCostFactor * (8 * L_w + 2) + 1700) + 600
      ≤ k * (lsfBatchCostFactor * (8 * L_w + 2) + 1700) + k * 600 := Nat.add_le_add_left h1 _
    _ = k * (lsfBatchCostFactor * (8 * L_w + 2) + 1700 + 600) := by ring
    _ ≤ k * (lsfBatchCostFactor * (7 * L_w + 1) + lsfBatchCostFactor * (6 * L_w)) :=
        Nat.mul_le_mul_left k h2

set_option maxHeartbeats 1200000 in
open Classical in
/-- Verification of `compStepInsCrossStmt` starting from the post-prefix state `stP` when `c1 ≠ c2`. -/
lemma compStepInsCross_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bCons bMark bDisp uPtr heap cntBase updBuf e a bVert : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {touched : List ℕ} {cnts : Fin k → ℕ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (_hpCons : p.procs[bCons]? = some ghostConsProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (htouch_nd : touched.Nodup)
    (htouch_lt : ∀ c ∈ touched, c < x.numComps)
    (hu_valid : (S ⟨0, hrep.1⟩).G.UpdateIsValid (.insert e a bVert))
    (heCap : e < x.eCap)
    (c1 c2 : Fin x.numComps) (h12 : c1 ≠ c2)
    (haC1 : a ∈ ((S ⟨0, hrep.1⟩).compSt (x.compOf c1)).G.V)
    (hbC2 : bVert ∈ ((S ⟨0, hrep.1⟩).compSt (x.compOf c2)).G.V)
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
      stP.regs 8 = x.vCap ∧ stP.regs 9 = x.eCap ∧ stP.regs 11 = c1.1 ∧ stP.regs 12 = c2.1 ∧
      stP.regs 16 = compTouchMarkBase b x.vCap x.eCap ∧ stP.regs 17 = heap + 1 ∧
      stP.regs 18 = compEdgefulBase b x.vCap ∧ stP.regs 19 = compEdgefulIdxBase b x.vCap)
    (hstP_mem : stP.mem = Function.update (Function.update (Function.update mem
      (compEdgeC1Base b x.vCap + e) c1.1) (compEdgeC2Base b x.vCap x.eCap + e) c2.1)
      (compIsInsBase b x.vCap x.eCap + e) 1) :
    let cs0 := S ⟨0, hrep.1⟩
    let S' : CompLSFFamily k := fun j => compLSFStepSingle (S j) (.insert e a bVert)
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (x' : CompLSFMeta k) (touched' : List ℕ) (cuts : Fin k → List (ℕ × ℕ)),
      Runs w p ω (compStepInsCrossStmt bCons bMark bDisp) stP .normal st' cost ∧
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
        compPhi b x mem + 460 +
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
  have hC2 : x.compOf c2 ∈ components cs0.G₀ := hT.compOf_mem c2
  have hCne : x.compOf c1 ≠ x.compOf c2 := fun h => h12 (hT.hBij.1 h)
  have ha_lt : a < x.vCap := hT.hVlt a hu_valid.2.1
  have hb_lt : bVert < x.vCap := hT.hVlt bVert hu_valid.2.2
  have ha_only : ∀ c : Fin x.numComps, a ∈ (cs0.compSt (x.compOf c)).G.V ↔ c = c1 := fun c =>
    ⟨fun h => by
      by_contra hne
      exact Finset.disjoint_left.mp (hI0.hV_disj _ (hT.compOf_mem c) _ hC1 (fun h' => hne (hT.hBij.1 h'))) h haC1,
     fun h => h ▸ haC1⟩
  have hb_only : ∀ c : Fin x.numComps, bVert ∈ (cs0.compSt (x.compOf c)).G.V ↔ c = c2 := fun c =>
    ⟨fun h => by
      by_contra hne
      exact Finset.disjoint_left.mp (hI0.hV_disj _ (hT.compOf_mem c) _ hC2 (fun h' => hne (hT.hBij.1 h'))) h hbC2,
     fun h => h ▸ hbC2⟩
  have htouch_iff : ∀ c : Fin x.numComps,
      x.compOf c ∈ touchedComps cs0 (.insert e a bVert) ↔ c = c1 ∨ c = c2 := fun c => by
    simp only [touchedComps, Finset.mem_filter, hT.compOf_mem c, true_and, projCompUpdateG, cs0,
      ha_only c, hb_only c]
    split_ifs <;> simp_all
  have hefComp_inj : ∀ ec₁ ec₂ : Fin x.numEdgeful, x.edgefulComp ec₁ = x.edgefulComp ec₂ → ec₁ = ec₂ := by
    intro ec₁ ec₂ heq; have h1 := (hEfMeta ec₁).2; have h2 := (hEfMeta ec₂).2
    rw [heq] at h1; exact Fin.ext (h1.symm.trans h2)
  set gPtr := compGhostBase b x.vCap x.eCap
  obtain ⟨stM2, cPre, touched', hrunPre, hcPre, hregsM2, htouch'_nd, htouch'_lt, htouch'_len,
    htouch'_iff, hcntM2, hlistM2, hM2_below_ec1, hM2_edges, hM2_ghost_ag, hM2_tm, hM2_above_tm⟩ :=
    compStepInsCrossPre_runs (bCons := bCons) (ω := ω) hpMark hw16
      ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩,
       hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩
      htouch_nd htouch_lt heCap c1 c2 h12 hend_heap hheap_cnt hcnt_buf hbuf_w
      hcnt_touch hlist_touch hstP_regs hstP_mem
  have htm_lt_end : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ x.endAddr := by
    have : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase,
        compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
        compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have hM2_ge_handles : ∀ z, compHandlesBase b x.vCap x.eCap x.L_w ≤ z → z < heap → stM2.mem z = mem z := fun z h1 h2 => by
    have hge_tm : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ z := by
      dsimp only [compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize,
        compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at h1 ⊢; omega
    exact hM2_above_tm z hge_tm (by omega) (Or.inl (by omega))
  have hM2_ge_cnt : ∀ z, cntBase ≤ z → stM2.mem z = mem z := fun z hz' =>
    hM2_above_tm z (by omega) (by omega) (Or.inr (by omega))
  -- Dispatch #1 `(c1, a)` and Dispatch #2 `(c2, bVert)` via insert-then-delete pairs
  have hwin_at_M2 : ∀ (c : Fin x.numComps), 1 ≤ (compGraph cs0.G₀ (x.compOf c)).m →
      ∃ ec : Fin x.numEdgeful, x.edgefulIdx c = ec.1 ∧
        stM2.mem (compEdgefulIdxBase b x.vCap + c.1) = ec.1 ∧ x.edgefulComp ec = c ∧
        CompDispatchWinOk W k b S x ec stM2.mem := fun c hpos => by
    obtain ⟨ec, hidx, hmem_idx, hcomp⟩ := (hCompMeta c).2.2.2 hpos
    have hwin_orig : CompDispatchWinOk W k b S x ec mem :=
      ⟨hk, hLw, hnumEf, hTE, hhdr.2.2.1, hhdr.1, hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
       fun j => (hBr j).2.2.2.2.2.2 (x.edgefulComp ec), fun j => hWins ec j,
       fun j₁ j₂ hne => hDisj ec ec j₁ j₂ (Or.inr hne)⟩
    refine ⟨ec, hidx, (hM2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; have := c.2; omega)).trans hmem_idx,
      hcomp, hwin_orig.of_agree
      ⟨hM2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compOffK]; omega),
       hM2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compOffVCap]; omega),
       hM2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compOffHandlesPtr]; omega)⟩
      (fun j => hM2_ge_handles _ (Nat.le_add_right _ _) (by
        have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        dsimp only [compTablesEnd] at hTE; omega))
      (fun j z hz => by
        obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
        have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
          dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz.1)
        exact hM2_ge_handles z hge_h (lt_of_lt_of_le hz.2 (le_trans hle hend_heap)))⟩
  have hu_c1_val : (cs0.compSt (x.compOf c1)).G.UpdateIsValid (.insert e a a) :=
    ⟨fun h => hu_valid.1 (hI0.hCE_sub _ hC1 h), haC1, haC1⟩
  obtain ⟨stD1, cD1, cuts1, winConc1, hrunD1, hregsD1, hbrD1, hwinD1, hfrD1, hzD1, hcostD1⟩ :=
    compStepInsDelPairDisp_runs (rC := 11) (rA := 6) (cnts := cnts) (st := stM2) (ω := ω)
      hpZero hpLogAdd hpPreLog hpLsf hpDisp hw16 hk hLw (by omega) (by omega) c1
      hefComp_inj (fun ec => (hEfMeta ec).1)
      ⟨ℓ₀, fun j => ⟨(hBr j).1, (hBr j).2.1, (hBr j).2.2.2.2.2.2 c1⟩⟩ hC1
      ((hregsM2 0 (by omega)).trans hstP_regs.1)
      ((hregsM2 3 (by omega)).trans hstP_regs.2.2.2.1)
      ((hregsM2 4 (by omega)).trans hstP_regs.2.2.2.2.1)
      ((hregsM2 5 (by omega)).trans hstP_regs.2.2.2.2.2.1)
      ((hregsM2 18 (by omega)).trans hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      ((hregsM2 19 (by omega)).trans hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      ((hregsM2 11 (by omega)).trans hstP_regs.2.2.2.2.2.2.2.2.2.2.1)
      ((hregsM2 6 (by omega)).trans hstP_regs.2.2.2.2.2.2.1)
      hnumC (by omega) hcnt_buf hbuf_w
      (fun z hz' => (hM2_ge_cnt z (by omega)).trans (hz z hz'))
      (fun j => (hM2_ge_cnt _ (Nat.le_add_right _ _)).trans (hcnts_m j))
      hTE ((hM2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; have := c1.2; omega)).trans (hCompMeta c1).1)
      (hwin_at_M2 c1)
      (fun j => by
        have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
        exact compRootCap_le_vCap (hBr j).1 hTj (hcnts_le j) c1 (.insert e a a))
      hu_c1_val heCap ha_lt
  let cnts1 : Fin k → ℕ := fun j => cnts j + (cuts1 j).length
  have hD1_below_tables : ∀ z < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k, stD1.mem z = stM2.mem z := fun z hz' =>
    hfrD1 z (fun ec j _ ha => by obtain ⟨_, _, _, _, _, hge, _⟩ := hWins ec j; exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hz' hge)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)
  have hwin_at_D1_c2 : 1 ≤ (compGraph cs0.G₀ (x.compOf c2)).m →
      ∃ ec : Fin x.numEdgeful, x.edgefulIdx c2 = ec.1 ∧
        stD1.mem (compEdgefulIdxBase b x.vCap + c2.1) = ec.1 ∧ x.edgefulComp ec = c2 ∧
        CompDispatchWinOk W k b S x ec stD1.mem := fun hpos => by
    obtain ⟨ec, hidx, hmi, hcomp, hwin2⟩ := hwin_at_M2 c2 hpos
    refine ⟨ec, hidx, (hD1_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; have := c2.2; omega)).trans hmi,
      hcomp, hwin2.of_agree
      ⟨hD1_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffK]; omega),
       hD1_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffVCap]; omega),
       hD1_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffHandlesPtr]; omega)⟩
      (fun j => hD1_below_tables _ (by
        have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        dsimp only [compTablesEnd]; omega))
      (fun j z hz => by
        obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j
        have hz_lt_end : z < x.endAddr := lt_of_lt_of_le hz.2 hle
        exact hfrD1 z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => h12 (h0.symm.trans (h ▸ hcomp)))) z hz ha0)
          (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega))⟩
  have hcap2 : ∀ j : Fin k, let Sj := (S j).compSt (x.compOf c2)
      cnts1 j + ((applyLSFUpdate Sj (.insert e bVert bVert)).R_orig \ Sj.R_orig).card ≤ x.vCap := by
    intro j Sj
    have hIj := (hBr j).1
    have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
    have hC1j : x.compOf c1 ∈ components (S j).G₀ := (hBr j).2.1.symm ▸ hC1
    have hC2j : x.compOf c2 ∈ components (S j).G₀ := (hBr j).2.1.symm ▸ hC2
    have hInv2 := LSFInvWith.toStructInv (hIj.hCompLSF _ hC2j).1
    have hNew2_sub_T0 : (applyLSFUpdate Sj (.insert e bVert bVert)).R_orig \ Sj.R_orig ⊆ Sj.T₀.V := fun r hr => by
      have hR0 : (applyLSFUpdate Sj (.insert e bVert bVert)).R₀_base ⊆ Sj.T₀.V := fun z hz => by
        simp only [applyLSFUpdate, Finset.mem_union, Finset.mem_filter] at hz
        exact hz.elim (fun h => hInv2.hR₀_sub h) (fun h => h.2)
      exact upClosure_subset (hldAuxTree_isRootedTree hInv2.hT₀) hR0 (Finset.mem_sdiff.mp hr).1
    have hNew2_sub_V2 : (applyLSFUpdate Sj (.insert e bVert bVert)).R_orig \ Sj.R_orig ⊆ Sj.G.V :=
      fun r hr => hInv2.hGV_eq ▸ Finset.mem_union_left _ (hNew2_sub_T0 hr)
    have hNew2_disj_R : Disjoint (S j).RF.R ((applyLSFUpdate Sj (.insert e bVert bVert)).R_orig \ Sj.R_orig) := by
      rw [Finset.disjoint_left]; intro r hrR hrN
      obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hrR
      have hD2 : D = x.compOf c2 := by
        by_contra hne
        exact Finset.disjoint_left.mp (hIj.hV_disj D hD _ hC2j hne)
          ((lsfInv_to_RS (hIj.hCompLSF D hD).1).2.2.1 hrD) (hNew2_sub_V2 hrN)
      subst hD2
      rcases Finset.mem_union.mp hrD with h1 | h2
      · exact (Finset.mem_sdiff.mp hrN).2 h1
      · exact Finset.disjoint_left.mp hInv2.hdisj_iso (hNew2_sub_T0 hrN) h2
    have hcuts1_sub_V1 : ((cuts1 j).map Prod.snd).toFinset ⊆ ((S j).compSt (x.compOf c1)).G.V := fun r hr => by
      by_cases hp1 : 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
        exact (LSFInvWith.toStructInv (hIj.hCompLSF _ hC1j).1).hT_cur_V ▸
          (compForestCutsValid_mem_E_V ((hbrD1 j).2.2.1 hp1).1 q hq).2
      · rw [(hbrD1 j).2.2.2 (by dsimp only [cs0] at hp1; omega)] at hr; simp at hr
    have hcuts1_disj_R : Disjoint (S j).RF.R ((cuts1 j).map Prod.snd).toFinset := by
      rw [Finset.disjoint_left]; intro r hrR hr1
      by_cases hp1 : 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m
      · have hr_not1 : r ∉ ((S j).compSt (x.compOf c1)).RF.R :=
          (Finset.mem_sdiff.mp (((hbrD1 j).2.2.1 hp1).2.2.2.2.2 ▸ hr1)).2
        obtain ⟨D, hD, hrD⟩ := Finset.mem_biUnion.mp hrR
        have hD1 : D = x.compOf c1 := by
          by_contra hne
          exact Finset.disjoint_left.mp (hIj.hV_disj D hD _ hC1j hne)
            ((lsfInv_to_RS (hIj.hCompLSF D hD).1).2.2.1 hrD) (hcuts1_sub_V1 hr1)
        exact hr_not1 (hD1 ▸ hrD)
      · rw [(hbrD1 j).2.2.2 (by dsimp only [cs0] at hp1; omega)] at hr1; simp at hr1
    have hcuts1_disj_N2 : Disjoint ((cuts1 j).map Prod.snd).toFinset
        ((applyLSFUpdate Sj (.insert e bVert bVert)).R_orig \ Sj.R_orig) :=
      Finset.disjoint_left.mpr fun r h1 h2 =>
        Finset.disjoint_left.mp (hIj.hV_disj _ hC1j _ hC2j hCne) (hcuts1_sub_V1 h1) (hNew2_sub_V2 h2)
    have hlen1 : (cuts1 j).length = ((cuts1 j).map Prod.snd).toFinset.card := by
      by_cases hp1 : 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m
      · rw [List.toFinset_card_of_nodup ((hbrD1 j).2.2.1 hp1).2.2.2.2.1, List.length_map]
      · rw [(hbrD1 j).2.2.2 (by dsimp only [cs0] at hp1; omega)]; simp
    have hun_sub : (S j).RF.R ∪ ((cuts1 j).map Prod.snd).toFinset ∪
        ((applyLSFUpdate Sj (.insert e bVert bVert)).R_orig \ Sj.R_orig) ⊆ Finset.range x.vCap := fun r hr => by
      refine Finset.mem_range.mpr (hTj.hVlt r ?_)
      rcases Finset.mem_union.mp hr with h12' | h3
      · rcases Finset.mem_union.mp h12' with h1 | h2
        · exact (compLSF_RF_isRSF hIj).2.2.1 h1
        · exact hIj.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c1, hC1j, hcuts1_sub_V1 h2⟩
      · exact hIj.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c2, hC2j, hNew2_sub_V2 h3⟩
    have hcard := Finset.card_le_card hun_sub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hNew2_disj_R, hcuts1_disj_N2⟩),
        Finset.card_union_of_disjoint hcuts1_disj_R, Finset.card_range] at hcard
    have := hcnts_le j; dsimp only [cnts1]; omega
  have hu_c2_val : (cs0.compSt (x.compOf c2)).G.UpdateIsValid (.insert e bVert bVert) :=
    ⟨fun h => hu_valid.1 (hI0.hCE_sub _ hC2 h), hbC2, hbC2⟩
  obtain ⟨stD2, cD2, cuts2, winConc2, hrunD2, hregsD2, hbrD2, hwinD2, hfrD2, hzD2, hcostD2⟩ :=
    compStepInsDelPairDisp_runs (rC := 12) (rA := 7) (cnts := cnts1) (st := stD1) (ω := ω)
      hpZero hpLogAdd hpPreLog hpLsf hpDisp hw16 hk hLw (by omega) (by omega) c2
      hefComp_inj (fun ec => (hEfMeta ec).1)
      ⟨ℓ₀, fun j => ⟨(hBr j).1, (hBr j).2.1, (hBr j).2.2.2.2.2.2 c2⟩⟩ hC2
      ((hregsD1 0 (by omega)).trans ((hregsM2 0 (by omega)).trans hstP_regs.1))
      ((hregsD1 3 (by omega)).trans ((hregsM2 3 (by omega)).trans hstP_regs.2.2.2.1))
      ((hregsD1 4 (by omega)).trans ((hregsM2 4 (by omega)).trans hstP_regs.2.2.2.2.1))
      ((hregsD1 5 (by omega)).trans ((hregsM2 5 (by omega)).trans hstP_regs.2.2.2.2.2.1))
      ((hregsD1 18 (by omega)).trans ((hregsM2 18 (by omega)).trans hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
      ((hregsD1 19 (by omega)).trans ((hregsM2 19 (by omega)).trans hstP_regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2))
      ((hregsD1 12 (by omega)).trans ((hregsM2 12 (by omega)).trans hstP_regs.2.2.2.2.2.2.2.2.2.2.2.1))
      ((hregsD1 7 (by omega)).trans ((hregsM2 7 (by omega)).trans hstP_regs.2.2.2.2.2.2.2.1))
      hnumC (by omega) hcnt_buf hbuf_w hzD1 (fun j => (hbrD1 j).1) hTE
      ((hD1_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase, compHdrSize]; have := c2.2; omega)).trans
        ((hM2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; have := c2.2; omega)).trans (hCompMeta c2).1))
      hwin_at_D1_c2 hcap2 hu_c2_val heCap hb_lt
  have hrun_all : Runs w p ω (compStepInsCrossStmt bCons bMark bDisp) stP .normal stD2 (cPre + cD1 + cD2 + 2) :=
    runs_seq_iff.mpr (Or.inr ⟨stM2, cPre, _, hrunPre,
      runs_seq_iff.mpr (Or.inr ⟨stD1, cD1, cD2, hrunD1, hrunD2, rfl⟩), by omega⟩)
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
      have hno0 : ¬ ∃ C ∈ components cs0.G₀, a ∈ (cs0.compSt C).G.V ∧ bVert ∈ (cs0.compSt C).G.V := by
        rintro ⟨C, hC, haC, hbC⟩; obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
        exact h12 (((ha_only c).mp haC).symm.trans ((hb_only c).mp hbC))
      have hnoj : ¬ ∃ C ∈ components (S j).G₀, a ∈ ((S j).compSt C).G.V ∧ bVert ∈ ((S j).compSt C).G.V := by
        rintro ⟨C, hC, haC, hbC⟩; obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp (hG0j ▸ hC)
        exact hno0 ⟨x.compOf c, hG0j ▸ hC, (hBr j).2.2.2.2.2.2 c ▸ haC, (hBr j).2.2.2.2.2.2 c ▸ hbC⟩
      rw [ite_eq_right hnoj, ite_eq_right hno0, (hBr j).2.2.2.2.1]
    · intro c
      have hG_c := applyLSFBatch_G_of_valid (hIj.hCompLSF _ (hG0j.symm ▸ hT.compOf_mem c)).1
        (projCompUpdateG_valid hIj hu_j (hG0j.symm ▸ hT.compOf_mem c))
      have hG_0 := applyLSFBatch_G_of_valid (hI0.hCompLSF _ (hT.compOf_mem c)).1
        (projCompUpdateG_valid hI0 hu_valid (hT.compOf_mem c))
      change (applyLSFBatch ((S j).compSt (x.compOf c)) _).G = (applyLSFBatch (cs0.compSt (x.compOf c)) _).G
      rw [hG_c, hG_0, hS_G j, (hBr j).2.2.2.2.2.2 c]
  have hT' := (compEdgeTrack_step_insert hI0 hT hu_valid heCap haC1 hbC2).of_ghostVerts
    (gtVert' := Function.update x.gtVert e (mem (ghostTVertBase gPtr x.vCap x.eCap + e)))
    (ghVert' := Function.update x.ghVert e (mem (ghostHVertBase gPtr x.vCap x.eCap + e)))
  have hcross_eq : (S' ⟨0, hk⟩).crossEdges = insert e cs0.crossEdges := by
    dsimp only [S', compLSFStepSingle]; refine ite_eq_right ?_
    rintro ⟨C, hC, haC, hbC⟩; obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
    exact h12 (((ha_only c).mp haC).symm.trans ((hb_only c).mp hbC))
  let winConc' : Fin x.numEdgeful → Fin k → LSFConcrete := fun ec j =>
    if x.edgefulComp ec = c1 then winConc1 ec j
    else if x.edgefulComp ec = c2 then winConc2 ec j
    else x.winConc ec j
  let cuts : Fin k → List (ℕ × ℕ) := fun j => cuts1 j ++ cuts2 j
  let x' : CompLSFMeta k :=
    { x with edgeC1 := Function.update x.edgeC1 e c1.1, edgeC2 := Function.update x.edgeC2 e c2.1,
             gtVert := Function.update x.gtVert e (mem (ghostTVertBase gPtr x.vCap x.eCap + e)),
             ghVert := Function.update x.ghVert e (mem (ghostHVertBase gPtr x.vCap x.eCap + e)),
             winConc := winConc' }
  have hD2_below_tables : ∀ z < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k, stD2.mem z = stM2.mem z := fun z hz' =>
    (hfrD2 z (fun ec j _ ha => by obtain ⟨_, _, _, _, _, hge, _⟩ := hWins ec j; exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hz' hge)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans (hD1_below_tables z hz')
  have hD2_below_ec1 : ∀ z < compEdgeC1Base b x.vCap, stD2.mem z = mem z := fun z hz' =>
    (hD2_below_tables z (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hz' ⊢; omega)).trans (hM2_below_ec1 z hz')
  have hD2_heap : stD2.mem heap = touched'.length :=
    (hfrD2 heap (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle hend_heap)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
    ((hfrD1 heap (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle hend_heap)))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans hcntM2)
  have hD2_list : ListAt stD2.mem (heap + 1) touched' := fun i hi =>
    (hfrD2 (heap + 1 + i) (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle (by omega))))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
    ((hfrD1 (heap + 1 + i) (fun ec j _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j; exact absurd ha.2 (not_lt.mpr (le_trans hle (by omega))))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans (hlistM2 i hi))
  -- Assemble `CompLSFRepDirty`
  have hrep' : CompLSFRepDirty W k b S' x' touched' stD2.mem := by
    refine ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE,
      compHeaderAt_of_agree hhdr (fun z _ hz2 => hD2_below_ec1 z (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hz2 ⊢; omega)),
      ⟨ℓ₀, hBr'⟩, hm0Tot, hT', ?_, hEfMeta, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c; dsimp only [x']; have hc_lt : c.1 < x.numComps := c.2; obtain ⟨h1, h2, h3, h4⟩ := hCompMeta c
      refine ⟨(hD2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)).trans h1,
        (hD2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base]; omega)).trans h2,
        (hD2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base]; omega)).trans h3, fun hpos => ?_⟩
      obtain ⟨ec, he1, he2, he3⟩ := h4 hpos
      exact ⟨ec, he1, (hD2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega)).trans he2, he3⟩
    · intro c v hv; dsimp only [x']
      have hv0 : v ∈ (cs0.compSt (x.compOf c)).G.V := by
        have hG := applyLSFBatch_G_of_valid (hI0.hCompLSF _ (hT.compOf_mem c)).1
          (projCompUpdateG_valid hI0 hu_valid (hT.compOf_mem c))
        have hVc : ((S' ⟨0, hk⟩).compSt (x.compOf c)).G.V = (cs0.compSt (x.compOf c)).G.V := by
          dsimp only [S', compLSFStepSingle]; rw [hG]; dsimp only [projCompUpdateG]; split_ifs <;> rfl
        exact hVc ▸ hv
      have hv_lt : v < x.vCap := hT.hVlt v (hI0.hV_eq ▸ Finset.mem_biUnion.mpr ⟨x.compOf c, hT.compOf_mem c, hv0⟩)
      exact (hD2_below_ec1 _ (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)).trans (hVComp c v hv0)
    · intro f hf; dsimp only [x']
      have hf_lt : f < x.eCap := by rcases Finset.mem_insert.mp hf with rfl | hf0; exact heCap; exact hT.hElt f hf0
      rw [hD2_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          hD2_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          (hM2_edges f hf_lt).1, (hM2_edges f hf_lt).2.1]
      by_cases hfe : f = e
      · subst hfe; simp
      · have hf0 : f ∈ cs0.G.E := (Finset.mem_insert.mp hf).resolve_left hfe
        simp [hfe, hEdgeC f hf0]
    · intro f hf; dsimp only [x'] at hf ⊢
      rw [hD2_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          hD2_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
          (hM2_edges f hf).2.2.1, (hM2_edges f hf).2.2.2, hcross_eq]
      change (if f = e then 1 else mem (compIsCrossBase b x.vCap x.eCap + f)) =
          (if f ∈ insert e cs0.crossEdges then 1 else 0) ∧
        (if f = e then 1 else mem (compIsInsBase b x.vCap x.eCap + f)) =
          (if f ∈ insert e cs0.insertedGlobal then 1 else 0)
      by_cases hfe : f = e
      · subst hfe; simp
      · simp [hfe, (hFlags f hf).1, (hFlags f hf).2, cs0]
    · dsimp only [x']
      have hD2_gh : ∀ z, gPtr ≤ z → z < compTouchMarkBase b x.vCap x.eCap → stD2.mem z = mem z := fun z h1 h2 =>
        (hD2_below_tables z (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at h2 ⊢; omega)).trans (hM2_ghost_ag z h1 h2)
      refine ⟨fun v hv => ?_, fun f hf hcr => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hGhost.1 v hv
        exact ⟨h1.of_agree
            (hD2_gh _ (by dsimp only [ghostTHeadBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTHeadBase, gPtr]; omega))
            (fun f hf => have := (hT.hGT v hv).2.1 f hf; hD2_gh _ (by dsimp only [ghostTPrevBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTPrevBase, gPtr]; omega))
            (fun f hf => have := (hT.hGT v hv).2.1 f hf; hD2_gh _ (by dsimp only [ghostTNextBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTNextBase, gPtr]; omega)),
          (hD2_gh _ (by dsimp only [ghostTCntBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTCntBase, gPtr]; omega)).trans h2,
          h3.of_agree
            (hD2_gh _ (by dsimp only [ghostHHeadBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHHeadBase, gPtr]; omega))
            (fun f hf => have := (hT.hGH v hv).2.1 f hf; hD2_gh _ (by dsimp only [ghostHPrevBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHPrevBase, gPtr]; omega))
            (fun f hf => have := (hT.hGH v hv).2.1 f hf; hD2_gh _ (by dsimp only [ghostHNextBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHNextBase, gPtr]; omega)),
          (hD2_gh _ (by dsimp only [ghostHCntBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHCntBase, gPtr]; omega)).trans h4⟩
      · have hf_lt : f < x.eCap := by rcases Finset.mem_insert.mp hf with rfl | hf0; exact heCap; exact hT.hElt f hf0
        rw [hD2_gh _ (by dsimp only [ghostTVertBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostTVertBase, gPtr]; omega),
            hD2_gh _ (by dsimp only [ghostHVertBase]; omega) (by dsimp only [compTouchMarkBase, compGhostSize, ghostHVertBase, gPtr]; omega)]
        by_cases hfe : f = e
        · subst hfe; simp [gPtr]
        · rw [hcross_eq] at hcr
          have hfcr : f ∈ cs0.crossEdges := (Finset.mem_insert.mp hcr).resolve_left hfe
          have hf0 : f ∈ cs0.G.E := (Finset.mem_insert.mp hf).resolve_left hfe
          simp only [Function.update_of_ne hfe]
          exact hGhost.2 f hf0 hfcr
    · intro c hc; dsimp only [x'] at hc ⊢
      rw [hD2_below_tables _ (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)]
      exact hM2_tm c hc
    · dsimp only [x']
      have hone_ag : ∀ i < x.L_w, stD2.mem (compOneLimbBase b x.vCap x.eCap + i) = mem (compOneLimbBase b x.vCap x.eCap + i) := fun i hi => by
        have hge_tm : compTouchMarkBase b x.vCap x.eCap + x.vCap ≤ compOneLimbBase b x.vCap x.eCap + i := by dsimp only [compOneLimbBase]; omega
        have h1e := compOneLimb_end_eq b x.vCap x.eCap x.L_w
        have hlt_te : compOneLimbBase b x.vCap x.eCap + i < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
          dsimp only [compTablesEnd]; omega
        exact (hD2_below_tables _ hlt_te).trans (hM2_above_tm _ hge_tm (by omega) (Or.inl (by omega)))
      exact ⟨(hone_ag 0 hLw).trans hOne.1, fun i h1 h2 => (hone_ag i h2).trans (hOne.2 i h1 h2)⟩
    · intro ec j; dsimp only [x']; have hec_lt : ec.1 < x.numEdgeful := ec.2
      obtain ⟨hslot, hrep_ec, hv, he, hL, hge, hle⟩ := hWins ec j
      have hslot' : stD2.mem (compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1)) = x.winHandle ec j := by
        have h1 : (ec.1 + 1) * k ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        exact (hD2_below_tables _ (by dsimp only [compTablesEnd]; omega)).trans ((hM2_ge_handles _ (Nat.le_add_right _ _) (by dsimp only [compTablesEnd] at hTE; omega)).trans hslot)
      by_cases hec1 : x.edgefulComp ec = c1
      · simp only [winConc', hec1, ↓reduceIte]
        obtain ⟨hss1, hrep1⟩ := (hwinD1 ec j).1 hec1
        have hrep1' : (LSFRep W.h).rep (x.winHandle ec j)
            (applyLSFBatch ((S j).compSt (x.compOf c1)) [.insert e a a, .delete e]) (winConc1 ec j) stD2.mem := by
          refine (lsfRep_local W.h _ _ _ stD1.mem stD2.mem fun z hz => ?_).1 hrep1
          symm
          have hz0 : (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) z := by simpa [LSFRep, hss1.endAddr] using hz
          have hz_lt_end : z < x.endAddr := lt_of_lt_of_le hz0.2 hle
          exact hfrD2 z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => h12 (hec1.symm.trans (h ▸ h0)))) z hz0 ha0)
            (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)
        have hSt_eq : (S' j).compSt (x.compOf c1) =
            applyLSFBatch ((S j).compSt (x.compOf c1)) [.insert e a a, .delete e] := by
          have ha_j : a ∈ ((S j).compSt (x.compOf c1)).G.V := ((hBr j).2.2.2.2.2.2 c1).symm ▸ haC1
          have hb_not : bVert ∉ ((S j).compSt (x.compOf c1)).G.V := by rw [(hBr j).2.2.2.2.2.2 c1]; exact fun h => h12 ((hb_only c1).mp h)
          change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
          simp [projCompUpdateG, ha_j, hb_not]
        exact ⟨hslot', hSt_eq ▸ hrep1', hss1.1.trans hv,
          hss1.2.1.trans he, hss1.2.2.2.2.2.2.2.2.1.trans hL, hge, (hss1.endAddr (x.winHandle ec j)).symm ▸ hle⟩
      · by_cases hec2 : x.edgefulComp ec = c2
        · simp only [winConc', hec2, h12.symm, ↓reduceIte]
          obtain ⟨hss2, hrep2⟩ := (hwinD2 ec j).1 hec2
          have hSt_eq : (S' j).compSt (x.compOf c2) =
              applyLSFBatch ((S j).compSt (x.compOf c2)) [.insert e bVert bVert, .delete e] := by
            have ha_not : a ∉ ((S j).compSt (x.compOf c2)).G.V := by rw [(hBr j).2.2.2.2.2.2 c2]; exact fun h => h12 ((ha_only c2).mp h).symm
            have hb_j : bVert ∈ ((S j).compSt (x.compOf c2)).G.V := ((hBr j).2.2.2.2.2.2 c2).symm ▸ hbC2
            change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
            simp [projCompUpdateG, ha_not, hb_j]
          exact ⟨hslot', hSt_eq ▸ hrep2, hss2.1.trans hv,
            hss2.2.1.trans he, hss2.2.2.2.2.2.2.2.2.1.trans hL, hge, (hss2.endAddr (x.winHandle ec j)).symm ▸ hle⟩
        · simp only [winConc', hec1, hec2, ↓reduceIte]
          have hSt_eq : (S' j).compSt (x.compOf (x.edgefulComp ec)) = (S j).compSt (x.compOf (x.edgefulComp ec)) := by
            have ha_not : a ∉ ((S j).compSt (x.compOf (x.edgefulComp ec))).G.V := by rw [(hBr j).2.2.2.2.2.2]; exact fun h => hec1 ((ha_only _).mp h)
            have hb_not : bVert ∉ ((S j).compSt (x.compOf (x.edgefulComp ec))).G.V := by rw [(hBr j).2.2.2.2.2.2]; exact fun h => hec2 ((hb_only _).mp h)
            change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
            simp [projCompUpdateG, ha_not, hb_not, applyLSFBatch]
          have hrep_old' : (LSFRep W.h).rep (x.winHandle ec j) ((S j).compSt (x.compOf (x.edgefulComp ec)))
              (x.winConc ec j) stD2.mem := by
            refine (lsfRep_local W.h _ _ _ mem stD2.mem fun z hz => ?_).1 hrep_ec
            have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ z := by
              dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) (le_trans hge hz.1)
            have hz_lt_end : z < x.endAddr := lt_of_lt_of_le hz.2 hle
            symm
            exact (hfrD2 z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hec2 (h ▸ h0))) z hz ha0)
              (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
              ((hfrD1 z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hec1 (h ▸ h0))) z hz ha0)
                (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)).trans
                (hM2_ge_handles z hge_h (lt_of_lt_of_le hz.2 (le_trans hle hend_heap))))
          exact ⟨hslot', hSt_eq ▸ hrep_old', hv, he, hL, hge, hle⟩
    · intro ec₁ ec₂ j₁ j₂ hne z h1 h2; dsimp only [x'] at h1 h2
      have hsame : ∀ ec j, (LSFRep W.h).foot (x.winHandle ec j) (winConc' ec j) z ↔
          (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) z := fun ec j => by
        dsimp only [winConc']; split_ifs with hc1 hc2
        · simp [LSFRep, ((hwinD1 ec j).1 hc1).1.endAddr]
        · simp [LSFRep, ((hwinD2 ec j).1 hc2).1.endAddr]
        · rfl
      exact hDisj ec₁ ec₂ j₁ j₂ hne z ((hsame ec₁ j₁).mp h1) ((hsame ec₂ j₂).mp h2)
  -- Potential & cost bound
  have hphi_old : compPhi b x mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) mem :=
    compPhi_eq_sum_dirty ⟨hk, hhW, hLinW, hPfpW, hLw, hhLw, heCap1, hnumC, hnumEf, hTE, hhdr,
      ⟨ℓ₀, hBr⟩, hm0Tot, hT, hCompMeta, hEfMeta, hVComp, hEdgeC, hFlags, hGhost, hTM, hOne, hWins, hDisj⟩
  have hphi_new : compPhi b x' stD2.mem =
      ∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD2.mem :=
    compPhi_eq_sum_dirty hrep'
  have hphi_M2 : (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) stM2.mem) =
      compPhi b x mem := by
    rw [hphi_old]; refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
    have hge_h : compHandlesBase b x.vCap x.eCap x.L_w ≤ x.winHandle ec j := by dsimp only [compTablesEnd] at hge; exact le_trans (Nat.le_add_right _ _) hge
    exact lsfPhi_congr fun z hz1 hz2 => hM2_ge_handles z (le_trans hge_h hz1) (lt_of_lt_of_le hz2 (le_trans hle hend_heap))
  have hcost_D1_sum : cD1 + 120 * (∑ j : Fin k, (cuts1 j).length) +
        (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) ≤
      (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) stM2.mem) +
      (if 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m then k * (lsfBatchCostFactor * (8 * x.L_w + 2) + 1700) + 600 else 40) := by
    by_cases hp1 : 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m
    · rw [dite_eq_left hp1] at hcostD1; rw [ite_eq_left hp1]
      obtain ⟨ec1, hec1, hle1⟩ := hcostD1
      rw [← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) (Finset.mem_univ ec1),
          ← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) stM2.mem) (Finset.mem_univ ec1)]
      have hrest : (∑ ec ∈ Finset.univ.erase ec1, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) =
          (∑ ec ∈ Finset.univ.erase ec1, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) stM2.mem) :=
        Finset.sum_congr rfl fun ec hec => Finset.sum_congr rfl fun j _ => by
          have hne_c : x.edgefulComp ec ≠ c1 := fun h => (Finset.mem_erase.mp hec).1 (hefComp_inj ec ec1 (h.trans hec1.symm))
          rw [(hwinD1 ec j).2 hne_c]; obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j
          exact lsfPhi_congr fun z hz1 hz2 => hfrD1 z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hne_c (h ▸ h0))) z ⟨hz1, hz2⟩ ha0)
            (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (lt_of_lt_of_le hz2 (le_trans hle (by omega)))
      rw [hrest]; linarith
    · rw [dite_eq_right hp1] at hcostD1; rw [ite_eq_right hp1]
      obtain ⟨hc1, hm1⟩ := hcostD1
      have hcuts0 : ∑ j : Fin k, (cuts1 j).length = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [(hbrD1 j).2.2.2 (by dsimp only [cs0] at hp1; omega)]; rfl
      have hpeq : (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) =
          (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) stM2.mem) :=
        Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => by
          rw [(hwinD1 ec j).2 (fun h => hp1 (h ▸ (hEfMeta ec).1))]; exact lsfPhi_congr fun z _ _ => hm1 z
      rw [hcuts0, hpeq]; omega
  have hcost_D2_sum : cD2 + 120 * (∑ j : Fin k, (cuts2 j).length) +
        (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD2.mem) ≤
      (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) +
      (if 1 ≤ (compGraph cs0.G₀ (x.compOf c2)).m then k * (lsfBatchCostFactor * (8 * x.L_w + 2) + 1700) + 600 else 40) := by
    by_cases hp2 : 1 ≤ (compGraph cs0.G₀ (x.compOf c2)).m
    · rw [dite_eq_left hp2] at hcostD2; rw [ite_eq_left hp2]
      obtain ⟨ec2, hec2, hle2⟩ := hcostD2
      have hec2_ne_c1 : x.edgefulComp ec2 ≠ c1 := by rw [hec2]; exact h12.symm
      rw [← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD2.mem) (Finset.mem_univ ec2),
          ← Finset.add_sum_erase Finset.univ (fun ec => ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) (Finset.mem_univ ec2)]
      have h2_eq_new : (∑ j : Fin k, lsfPhi (x.winHandle ec2 j) (winConc' ec2 j) stD2.mem) =
          (∑ j : Fin k, lsfPhi (x.winHandle ec2 j) (winConc2 ec2 j) stD2.mem) :=
        Finset.sum_congr rfl fun j _ => by simp [winConc', hec2, h12.symm]
      have h2_eq_old : (∑ j : Fin k, lsfPhi (x.winHandle ec2 j) (winConc1 ec2 j) stD1.mem) =
          (∑ j : Fin k, lsfPhi (x.winHandle ec2 j) (x.winConc ec2 j) stD1.mem) :=
        Finset.sum_congr rfl fun j _ => by rw [(hwinD1 ec2 j).2 hec2_ne_c1]
      have hrest : (∑ ec ∈ Finset.univ.erase ec2, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD2.mem) =
          (∑ ec ∈ Finset.univ.erase ec2, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) :=
        Finset.sum_congr rfl fun ec hec => Finset.sum_congr rfl fun j _ => by
          have hne_c2 : x.edgefulComp ec ≠ c2 := fun h => (Finset.mem_erase.mp hec).1 (hefComp_inj ec ec2 (h.trans hec2.symm))
          have hwc_eq : winConc' ec j = winConc1 ec j := by
            by_cases hc1 : x.edgefulComp ec = c1
            · simp [winConc', hc1]
            · simp [winConc', hc1, hne_c2, (hwinD1 ec j).2 hc1]
          rw [hwc_eq]
          have hss_end : (winConc1 ec j).endAddr (x.winHandle ec j) = (x.winConc ec j).endAddr (x.winHandle ec j) := by
            by_cases hc1 : x.edgefulComp ec = c1; exact ((hwinD1 ec j).1 hc1).1.endAddr _; rw [(hwinD1 ec j).2 hc1]
          obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j
          refine lsfPhi_congr fun z hz1 hz2 => ?_
          have hz0 : (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) z := by simpa [LSFRep, hss_end] using And.intro hz1 hz2
          exact hfrD2 z (fun ec0 j0 h0 ha0 => hDisj ec ec0 j j0 (Or.inl (fun h => hne_c2 (h ▸ h0))) z hz0 ha0)
            (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (lt_of_lt_of_le hz0.2 (le_trans hle (by omega)))
      rw [h2_eq_new, h2_eq_old, hrest]; linarith
    · rw [dite_eq_right hp2] at hcostD2; rw [ite_eq_right hp2]
      obtain ⟨hc2, hm2⟩ := hcostD2
      have hcuts0 : ∑ j : Fin k, (cuts2 j).length = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [(hbrD2 j).2.2.2 (by dsimp only [cs0] at hp2; omega)]; rfl
      have hpeq : (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) stD2.mem) =
          (∑ ec : Fin x.numEdgeful, ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc1 ec j) stD1.mem) :=
        Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => by
          have hne_c2 : x.edgefulComp ec ≠ c2 := fun h => hp2 (h ▸ (hEfMeta ec).1)
          have hwc_eq : winConc' ec j = winConc1 ec j := by
            by_cases hc1 : x.edgefulComp ec = c1
            · simp [winConc', hc1]
            · simp [winConc', hc1, hne_c2, (hwinD1 ec j).2 hc1]
          rw [hwc_eq]; exact lsfPhi_congr fun z _ _ => hm2 z
      rw [hcuts0, hpeq]; omega
  have hcost_final :
      (cPre + cD1 + cD2 + 2) + 120 * (∑ j : Fin k, (cuts j).length) + compPhi b x' stD2.mem ≤
      compPhi b x mem + 460 +
      k * ((touchedComps cs0 (.insert e a bVert)).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
        lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.insert e a bVert)) * x.L_w + 1) +
        lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.insert e a bVert) * x.L_w)) := by
    have hcuts_sum : (∑ j : Fin k, (cuts j).length) = (∑ j : Fin k, (cuts1 j).length) + (∑ j : Fin k, (cuts2 j).length) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => List.length_append
    have hsum_eq : ((touchedComps cs0 (.insert e a bVert)).filter fun C => 1 ≤ (compGraph cs0.G₀ C).m).sum (fun C =>
          lsfBatchCostFactor * ((1 + projUpdWords mem cs0 C uPtr (.insert e a bVert)) * x.L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem cs0 C uPtr (.insert e a bVert) * x.L_w)) =
        (if 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m then lsfBatchCostFactor * (7 * x.L_w + 1) + lsfBatchCostFactor * (6 * x.L_w) else 0) +
        (if 1 ≤ (compGraph cs0.G₀ (x.compOf c2)).m then lsfBatchCostFactor * (7 * x.L_w + 1) + lsfBatchCostFactor * (6 * x.L_w) else 0) := by
      have hS_eq : (touchedComps cs0 (.insert e a bVert)).filter (fun C => 1 ≤ (compGraph cs0.G₀ C).m) =
          ({x.compOf c1, x.compOf c2} : Finset (Finset ℕ)).filter (fun C => 1 ≤ (compGraph cs0.G₀ C).m) := by
        ext C; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        by_cases hC : C ∈ components cs0.G₀
        · obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC; rw [htouch_iff c, hT.hBij.1.eq_iff, hT.hBij.1.eq_iff]
        · have hnot : C ∉ touchedComps cs0 (.insert e a bVert) := fun h => hC (Finset.mem_filter.mp h).1
          simp [hnot, show C ≠ x.compOf c1 from fun h => hC (h ▸ hC1), show C ≠ x.compOf c2 from fun h => hC (h ▸ hC2)]
      rw [hS_eq, Finset.sum_filter, Finset.sum_pair hCne]
      have hb_not1 : bVert ∉ (cs0.compSt (x.compOf c1)).G.V := fun h => h12 ((hb_only c1).mp h)
      have ha_not2 : a ∉ (cs0.compSt (x.compOf c2)).G.V := fun h => h12 ((ha_only c2).mp h).symm
      have hpw1 : projUpdWords mem cs0 (x.compOf c1) uPtr (.insert e a bVert) = 6 := by
        simp [projUpdWords, hb_not1, cs0, haC1]
      have hpw2 : projUpdWords mem cs0 (x.compOf c2) uPtr (.insert e a bVert) = 6 := by
        simp [projUpdWords, ha_not2, cs0, hbC2]
      rw [hpw1, hpw2]
    rw [hphi_new, hcuts_sum, hsum_eq, Nat.mul_add]
    have habs := compPairDispatch_cost_le hk hLw
    by_cases hp1 : 1 ≤ (compGraph cs0.G₀ (x.compOf c1)).m <;> by_cases hp2 : 1 ≤ (compGraph cs0.G₀ (x.compOf c2)).m <;>
      simp only [hp1, hp2, ↓reduceIte] at hcost_D1_sum hcost_D2_sum ⊢ <;> linarith
  -- Final assembly
  refine ⟨stD2, cPre + cD1 + cD2 + 2, x', touched', cuts, hrun_all,
    (hregsD2 1 (by omega)).trans ((hregsD1 1 (by omega)).trans ((hregsM2 1 (by omega)).trans hstP_regs.2.1)),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
    hrep', htouch'_nd, htouch'_lt, htouch'_len,
    fun c => by rw [htouch'_iff c, htouch_iff c],
    hD2_heap, hD2_list, ?_, ?_, hzD2, hcost_final⟩
  · intro j
    have hTj := compEdgeTrack_of_same_graph hT (hBr j).2.1 (hS_G j) (hBr j).2.2.2.2.1 (hBr j).2.2.2.2.2.2
    have hG0j := (hBr j).2.1
    have hC1j : x.compOf c1 ∈ components (S j).G₀ := hG0j.symm ▸ hC1
    have hC2j : x.compOf c2 ∈ components (S j).G₀ := hG0j.symm ▸ hC2
    have hSelf1 : (S' j).compSt (x.compOf c1) =
        applyLSFBatch ((S j).compSt (x.compOf c1)) [.insert e a a, .delete e] := by
      have ha_j : a ∈ ((S j).compSt (x.compOf c1)).G.V := ((hBr j).2.2.2.2.2.2 c1).symm ▸ haC1
      have hb_not : bVert ∉ ((S j).compSt (x.compOf c1)).G.V := by rw [(hBr j).2.2.2.2.2.2 c1]; exact fun h => h12 ((hb_only c1).mp h)
      change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
      simp [projCompUpdateG, ha_j, hb_not]
    have hSelf2 : (S' j).compSt (x.compOf c2) =
        applyLSFBatch ((S j).compSt (x.compOf c2)) [.insert e bVert bVert, .delete e] := by
      have ha_not : a ∉ ((S j).compSt (x.compOf c2)).G.V := by rw [(hBr j).2.2.2.2.2.2 c2]; exact fun h => h12 ((ha_only c2).mp h).symm
      have hb_j : bVert ∈ ((S j).compSt (x.compOf c2)).G.V := ((hBr j).2.2.2.2.2.2 c2).symm ▸ hbC2
      change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
      simp [projCompUpdateG, ha_not, hb_j]
    have hRF1 := applyLSFBatch_insert_delete_selfLoop_RF ((hBr j).1.hCompLSF _ hC1j).1
      (fun h => hu_valid.1 (hI0.hCE_sub _ hC1 ((hBr j).2.2.2.2.2.2 c1 ▸ h)))
      (((hBr j).2.2.2.2.2.2 c1).symm ▸ haC1)
    have hRF2 := applyLSFBatch_insert_delete_selfLoop_RF ((hBr j).1.hCompLSF _ hC2j).1
      (fun h => hu_valid.1 (hI0.hCE_sub _ hC2 ((hBr j).2.2.2.2.2.2 c2 ▸ h)))
      (((hBr j).2.2.2.2.2.2 c2).symm ▸ hbC2)
    have hOther : ∀ D ∈ components (S j).G₀, D ≠ x.compOf c1 → D ≠ x.compOf c2 → (S' j).compSt D = (S j).compSt D := by
      intro D hD hne1 hne2
      obtain ⟨c, rfl⟩ := (hTj.hBij.2 D).mp hD
      have hnec1 : c ≠ c1 := fun h => hne1 (h ▸ rfl)
      have hnec2 : c ≠ c2 := fun h => hne2 (h ▸ rfl)
      have ha_not : a ∉ ((S j).compSt (x.compOf c)).G.V := by rw [(hBr j).2.2.2.2.2.2 c]; exact fun h => hnec1 ((ha_only c).mp h)
      have hb_not : bVert ∉ ((S j).compSt (x.compOf c)).G.V := by rw [(hBr j).2.2.2.2.2.2 c]; exact fun h => hnec2 ((hb_only c).mp h)
      change applyLSFBatch _ (projCompUpdateG (S j).G _ (.insert e a bVert)) = _
      simp [projCompUpdateG, ha_not, hb_not, applyLSFBatch]
    have hlift := compRF_cuts_lift_two_insDel (hBr j).1 hTj ((hS_G j).symm ▸ hu_valid) h12
      (by rw [hSelf1]; exact hRF1.2.1) (by rw [hSelf1]; exact hRF1.2.2)
      (by rw [hSelf2]; exact hRF2.2.1) (by rw [hSelf2]; exact hRF2.2.2)
      hOther (by rw [hSelf1]; rfl) (by rw [hSelf2]; rfl)
      (fun hp => let h := (hbrD1 j).2.2.1 (by simpa [hG0j] using hp); ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)
      (fun hm => (hbrD1 j).2.2.2 (by simpa [hG0j] using hm))
      (fun hp => let h := (hbrD2 j).2.2.1 (by simpa [hG0j] using hp); ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)
      (fun hm => (hbrD2 j).2.2.2 (by simpa [hG0j] using hm))
    obtain ⟨hval, hndE, hsE, hEsub, hndR, hsR, hRsub⟩ := hlift
    have hcnt_le_new := compStep_cnts_le_of_lift (hcnts_le j) hRsub hndR hsR
    have hlen2_all : ∀ j0 : Fin k, cnts j0 + (cuts1 j0).length + (cuts2 j0).length ≤ x.vCap := fun j0 => by
      by_cases hp2 : 1 ≤ (compGraph cs0.G₀ (x.compOf c2)).m
      · have hcard2 := List.toFinset_card_of_nodup ((hbrD2 j0).2.2.1 hp2).2.2.2.2.1
        rw [List.length_map, ((hbrD2 j0).2.2.1 hp2).2.2.2.2.2] at hcard2
        have hsub : ((applyLSFUpdate ((S j0).compSt (x.compOf c2)) (.insert e bVert bVert)).RF.R \
            ((S j0).compSt (x.compOf c2)).RF.R) ⊆
            ((applyLSFUpdate ((S j0).compSt (x.compOf c2)) (.insert e bVert bVert)).R_orig \
            ((S j0).compSt (x.compOf c2)).R_orig) := fun z hz => by
          simp only [LSFState.RF, LSFState.R, applyLSFUpdate, Finset.mem_sdiff, Finset.mem_union] at hz ⊢
          exact ⟨hz.1.resolve_right (fun h => hz.2 (Or.inr h)), fun h => hz.2 (Or.inl h)⟩
        have hcap2_j0 := hcap2 j0; dsimp only [cnts1] at hcap2_j0
        have := Finset.card_le_card hsub; omega
      · rw [(hbrD2 j0).2.2.2 (by dsimp only [cs0] at hp2; omega)]; simp
        have hcap2_j0 := hcap2 j0; dsimp only [cnts1] at hcap2_j0; omega
    have hcnt_j : stD2.mem (cntBase + j.1) = cnts j + (cuts j).length := by
      have := (hbrD2 j).1; dsimp only [cnts1, cuts] at this ⊢; rw [this, List.length_append, Nat.add_assoc]
    have hbuf_j : ∀ i (hi : i < (cuts j).length),
        stD2.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
        stD2.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1 := by
      intro i hi
      by_cases h1 : i < (cuts1 j).length
      · have hdisj_i := compStep_cutBuf_disj (cntBase := cntBase) hlen2_all j h1
        have hfr_r := hfrD2 (rootsBase + j.1 * x.vCap + (cnts j + i))
          (fun ec j0 _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j0; exact absurd ha.2 (not_lt.mpr (le_trans hle (by omega))))
          (fun j0 => (hdisj_i.1 j0).1) (fun j0 => (hdisj_i.2.1 j0).1) (fun j0 => (hdisj_i.2.2.1 j0).1) (by omega)
        have hfr_f := hfrD2 (fDelBase + j.1 * x.vCap + (cnts j + i))
          (fun ec j0 _ ha => by obtain ⟨_, _, _, _, _, _, hle⟩ := hWins ec j0; exact absurd ha.2 (not_lt.mpr (le_trans hle (by omega))))
          (fun j0 => (hdisj_i.1 j0).2) (fun j0 => (hdisj_i.2.1 j0).2) (fun j0 => (hdisj_i.2.2.1 j0).2) (by omega)
        have hb1 := (hbrD1 j).2.1 i h1
        simpa [cuts, List.getElem_append_left h1] using ⟨hfr_r.trans hb1.1, hfr_f.trans hb1.2⟩
      · have h2 : i - (cuts1 j).length < (cuts2 j).length := by dsimp only [cuts] at hi; rw [List.length_append] at hi; omega
        have hb2 := (hbrD2 j).2.1 (i - (cuts1 j).length) h2
        have heq_idx : cnts1 j + (i - (cuts1 j).length) = cnts j + i := by dsimp only [cnts1]; omega
        rw [heq_idx] at hb2
        simpa [cuts, List.getElem_append_right (by omega : (cuts1 j).length ≤ i)] using hb2
    exact ⟨hcnt_j, hbuf_j, hval, hndE, hsE, hEsub, hndR, hsR, hRsub, hcnt_le_new⟩
  · intro z hout hnh hnl hnc hnrt hnfd hlt_buf
    have hwin_out : ∀ ec j, ¬ (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) z := fun ec j ha => by
      obtain ⟨_, _, _, _, _, hge, hle⟩ := hWins ec j
      have hb_le : b ≤ x.winHandle ec j := by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hge; omega
      rcases hout with hlt | hge'
      · exact absurd ha.1 (not_le.mpr (lt_of_lt_of_le hlt hb_le))
      · exact absurd ha.2 (not_lt.mpr (le_trans hle hge'))
    have h1 : stD2.mem z = stD1.mem z := hfrD2 z (fun ec j _ => hwin_out ec j) hnc
      (fun j => by have := hnrt j; dsimp only [cnts1, cuts] at this ⊢; rw [List.length_append] at this; omega)
      (fun j => by have := hnfd j; dsimp only [cnts1, cuts] at this ⊢; rw [List.length_append] at this; omega) hlt_buf
    have h2 : stD1.mem z = stM2.mem z := hfrD1 z (fun ec j _ => hwin_out ec j) hnc
      (fun j => by have := hnrt j; dsimp only [cuts] at this ⊢; rw [List.length_append] at this; omega)
      (fun j => by have := hnfd j; dsimp only [cuts] at this ⊢; rw [List.length_append] at this; omega) hlt_buf
    rw [h1, h2]
    rcases hout with hlt | hge'
    · exact hM2_below_ec1 z (by dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
    · exact hM2_above_tm z (by omega) hnh hnl

end

end MinCostFlow.SparseCore.Program
