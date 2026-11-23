module

public import MinCostFlow.SparseCore.Program.CompBatchStepSplitBase
import WordRAM.Tactic

/-!
# Vertex-Split Step: Conditional Dispatch (`CompBatchStepSplitDisp`)

Verifies `compStepSplitDispStmt`: if component `cv` is edgeful, builds the projected 1-update
split batch (filtering out cross-edges uniformly for Tag 2 and Tag 3) and dispatches it across all
`k` branches; otherwise leaves memory unchanged in `O(1)` time.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 1200000 in
open Classical in
/-- Verification of `compStepSplitDispStmt bApp bDisp` for a split `.split v v' St Sh` on
component `cv`. -/
theorem compStepSplitDisp_runs {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bApp bDisp uPtr cntBase updBuf tag v v' : ℕ}
    {St Sh : Finset ℕ} {Lt Lh : List ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k} {cnts : Fin k → ℕ}
    {st : State} {ω : ℕ → Bool}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (_hpApp : p.procs[bApp]? = some ghostAppendProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hw16 : 16 ≤ 2 ^ w) (hk : 1 ≤ k) (hLw : 1 ≤ x.L_w)
    (htag : tag = 2 ∨ tag = 3)
    (cv : Fin x.numComps)
    (hefComp_inj : ∀ ec₁ ec₂ : Fin x.numEdgeful, x.edgefulComp ec₁ = x.edgefulComp ec₂ → ec₁ = ec₂)
    (hef_pos : ∀ ec : Fin x.numEdgeful, 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf (x.edgefulComp ec))).m)
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = uPtr) (hr3 : st.regs 3 = cntBase)
    (hr4 : st.regs 4 = updBuf) (hr6 : st.regs 6 = tag) (hr7 : st.regs 7 = v)
    (hr8 : st.regs 8 = v') (hr9 : st.regs 9 = Lt.length) (hr10 : st.regs 10 = Lh.length)
    (hr12 : st.regs 12 = cv.1) (hr15 : st.regs 15 = compEdgefulBase b x.vCap)
    (hr16 : st.regs 16 = compEdgefulIdxBase b x.vCap)
    (hnumC : x.numComps ≤ x.vCap)
    (hend_le : x.endAddr ≤ cntBase)
    (hcnt_buf : cntBase + k + 2 * (k * x.vCap) ≤ updBuf)
    (hu_disj : uPtr + (5 + Lt.length + Lh.length) ≤ updBuf)
    (hbuf_w : updBuf + 6 + Lt.length + Lh.length < 2 ^ w)
    (hz : ZeroFrom st.mem updBuf)
    (hcnts_m : ∀ j : Fin k, st.mem (cntBase + j.1) = cnts j)
    (hTE : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr)
    (hef_m : st.mem (compEdgefulBase b x.vCap + cv.1) =
      if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf cv)).m then 1 else 0)
    (hef_spec : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf cv)).m →
      ∃ ec : Fin x.numEdgeful, x.edgefulIdx cv = ec.1 ∧
        st.mem (compEdgefulIdxBase b x.vCap + cv.1) = ec.1 ∧ x.edgefulComp ec = cv ∧
        CompDispatchWinOk W k b S x ec st.mem)
    (hI0 : ∃ ℓ₀, CompLSFInv W.C_lsst ℓ₀ (S ⟨0, hk⟩))
    (hT : CompEdgeTrack x.numComps x.vCap x.eCap x.compOf x.edgeC1 x.edgeC2 x.gtVert x.ghVert
      x.gtList x.ghList (S ⟨0, hk⟩))
    (hu_valid_g : (S ⟨0, hk⟩).G.UpdateIsValid (.split v v' St Sh))
    (hvC : v ∈ ((S ⟨0, hk⟩).compSt (x.compOf cv)).G.V)
    (hv_lt : v < x.vCap) (hv'_lt : v' < x.vCap)
    (hLt_at : ListAt st.mem (uPtr + 5) Lt)
    (hLh_at : ListAt st.mem (uPtr + 5 + Lt.length) Lh)
    (hLt_nd : Lt.Nodup) (hLh_nd : Lh.Nodup)
    (hLt_mem : tag = 2 → ∀ e, e ∈ Lt ↔ e ∈ (S ⟨0, hk⟩).G.E ∧ (S ⟨0, hk⟩).G.tail e = v ∧ e ∈ St)
    (hLh_mem : tag = 2 → ∀ e, e ∈ Lh ↔ e ∈ (S ⟨0, hk⟩).G.E ∧ (S ⟨0, hk⟩).G.head e = v ∧ e ∈ Sh)
    (hLt_mem3 : tag = 3 → ∀ e, e ∈ Lt ↔ e ∈ (S ⟨0, hk⟩).G.E ∧ (S ⟨0, hk⟩).G.tail e = v ∧ e ∉ St)
    (hLh_mem3 : tag = 3 → ∀ e, e ∈ Lh ↔ e ∈ (S ⟨0, hk⟩).G.E ∧ (S ⟨0, hk⟩).G.head e = v ∧ e ∉ Sh)
    (hLt_w : ∀ e ∈ Lt, e < 2 ^ w) (hLh_w : ∀ e ∈ Lh, e < 2 ^ w)
    (hcr_ptr : st.mem (b + compOffIsCrossPtr) = compIsCrossBase b x.vCap x.eCap)
    (hcr_m : ∀ e < x.eCap, st.mem (compIsCrossBase b x.vCap x.eCap + e) =
      if e ∈ (S ⟨0, hk⟩).crossEdges then 1 else 0)
    (hcap : ∀ j : Fin k,
      let Sj := (S j).compSt (x.compOf cv)
      let StC := Sj.G.E.filter fun e => e ∈ St ∧ Sj.G.tail e = v ∧ (S ⟨0, hk⟩).G.tail e = v
      let ShC := Sj.G.E.filter fun e => e ∈ Sh ∧ Sj.G.head e = v ∧ (S ⟨0, hk⟩).G.head e = v
      cnts j + ((applyLSFUpdate Sj (.split v v' StC ShC)).R_orig \ Sj.R_orig).card ≤ x.vCap) :
    let cs0 := S ⟨0, hk⟩
    let Gc := (cs0.compSt (x.compOf cv)).G
    let StC := Gc.E.filter fun e => e ∈ St ∧ Gc.tail e = v ∧ cs0.G.tail e = v
    let ShC := Gc.E.filter fun e => e ∈ Sh ∧ Gc.head e = v ∧ cs0.G.head e = v
    let u_c := Update.split v v' StC ShC
    let len := 5 + Lt.length + Lh.length
    let rootsBase := cntBase + k
    let fDelBase := cntBase + k + k * x.vCap
    ∃ st' cost, ∃ (cuts : Fin k → List (ℕ × ℕ)) (winConc' : Fin x.numEdgeful → Fin k → LSFConcrete),
      Runs w p ω (compStepSplitDispStmt bApp bDisp) st .normal st' cost ∧
      (∀ r < 19, st'.regs r = st.regs r) ∧
      (∀ j : Fin k,
        let Sj := (S j).compSt (x.compOf cv)
        let Sj' := applyLSFUpdate Sj u_c
        st'.mem (cntBase + j.1) = cnts j + (cuts j).length ∧
        (∀ i (hi : i < (cuts j).length),
          st'.mem (rootsBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].2 ∧
          st'.mem (fDelBase + j.1 * x.vCap + (cnts j + i)) = (cuts j)[i].1) ∧
        (1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m →
          CompForestCutsValid x.vCap Sj.RF (cuts j) ∧
          ((cuts j).foldl compApplyForestCut Sj.RF).F.E = Sj'.RF.F.E ∧
          ((cuts j).map Prod.fst).Nodup ∧
          ((cuts j).map Prod.fst).toFinset = Sj.RF.F.E \ Sj'.RF.F.E ∧
          ((cuts j).map Prod.snd).Nodup ∧
          Sj'.RF.R = insert v' (Sj.RF.R ∪ ((cuts j).map Prod.snd).toFinset) ∧
          v' ∉ Sj.RF.R ∪ ((cuts j).map Prod.snd).toFinset ∧
          ((cuts j).map Prod.snd).toFinset = Sj'.RF.R.erase v' \ Sj.RF.R) ∧
        ((compGraph cs0.G₀ (x.compOf cv)).m = 0 → cuts j = [])) ∧
      (∀ (ec : Fin x.numEdgeful) (j : Fin k),
        (x.edgefulComp ec = cv →
          SameStaticConcrete (x.winConc ec j) (winConc' ec j) ∧
          (LSFRep W.h).rep (x.winHandle ec j) (applyLSFUpdate ((S j).compSt (x.compOf cv)) u_c)
            (winConc' ec j) st'.mem) ∧
        (x.edgefulComp ec ≠ cv → winConc' ec j = x.winConc ec j)) ∧
      (∀ a,
        (∀ ec j, x.edgefulComp ec = cv → ¬ (LSFRep W.h).foot (x.winHandle ec j) (x.winConc ec j) a) →
        (∀ j : Fin k, a ≠ cntBase + j.1) →
        (∀ j : Fin k, a < rootsBase + j.1 * x.vCap + cnts j ∨
          rootsBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        (∀ j : Fin k, a < fDelBase + j.1 * x.vCap + cnts j ∨
          fDelBase + j.1 * x.vCap + cnts j + (cuts j).length ≤ a) →
        a < updBuf → st'.mem a = st.mem a) ∧
      ZeroFrom st'.mem updBuf ∧
      (if _ : 1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m then
        ∃ ec : Fin x.numEdgeful, x.edgefulComp ec = cv ∧
          cost + 120 * (∑ j : Fin k, (cuts j).length) +
              (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) st'.mem) ≤
            k * (lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + 850) + 65 * len + 450 +
              (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) st.mem)
      else cost ≤ 20 ∧ ∀ a, st'.mem a = st.mem a) := by
  intro cs0 Gc StC ShC u_c len rootsBase fDelBase
  obtain ⟨ℓ₀, hInv0⟩ := hI0
  have hef_w : compEdgefulBase b x.vCap + cv.1 < 2 ^ w := by
    have : compEdgefulBase b x.vCap + cv.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase, compHdrSize]
      have := cv.2; omega
    omega
  have hefIdx_w : compEdgefulIdxBase b x.vCap + cv.1 < 2 ^ w := by
    have : compEdgefulIdxBase b x.vCap + cv.1 < compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase, compEdgefulBase,
        compVCompBase, compHdrSize]; have := cv.2; omega
    omega
  have hLt_lt : ∀ e ∈ Lt, e < x.eCap := fun e he => by
    rcases htag with rfl | rfl
    · exact hT.hElt e ((hLt_mem rfl e).mp he).1
    · exact hT.hElt e ((hLt_mem3 rfl e).mp he).1
  have hLh_lt : ∀ e ∈ Lh, e < x.eCap := fun e he => by
    rcases htag with rfl | rfl
    · exact hT.hElt e ((hLh_mem rfl e).mp he).1
    · exact hT.hElt e ((hLh_mem3 rfl e).mp he).1
  set efFlag := if 1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m then 1 else 0
  let st1 : State := { st with regs := Function.update st.regs 19 efFlag }
  have hs1 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 15) (.reg 12)))) st .normal st1 5 := by
    rw [runs_assign_iff]; refine ⟨efFlag, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [Expr.eval, BinOp.eval, hr15, hr12, hef_w, hef_m, efFlag]
  by_cases hpos : 1 ≤ (compGraph cs0.G₀ (x.compOf cv)).m
  · have hef1 : efFlag = 1 := ite_eq_left hpos
    obtain ⟨ec, _, hmi, hcomp, hwin⟩ := hef_spec hpos
    obtain ⟨stB, cB, hrunB, hrB_lt19, hrB_23, hB_num, hB_list, hfrB, hcB⟩ :=
      compStepSplitBuild_runs (bApp := bApp) (tag := tag) (v := v) (v' := v') (st := st1) (ω := ω) hw16
        (by simp [st1, hr0]) (by simp [st1, hr1]) (by simp [st1, hr4]) (by simp [st1, hr6])
        (by simp [st1, hr7]) (by simp [st1, hr8]) (by simp [st1, hr9]) (by simp [st1, hr10])
        hTE (by omega) hu_disj hbuf_w hLt_at hLh_at hLt_lt hLh_lt hcr_ptr
    set crBase := compIsCrossBase b x.vCap x.eCap
    set Lt' := Lt.filter fun e => decide (st.mem (crBase + e) = 0)
    set Lh' := Lh.filter fun e => decide (st.mem (crBase + e) = 0)
    set len' := 5 + Lt'.length + Lh'.length
    have hlen'_le : len' ≤ len := by
      have h1 : Lt'.length ≤ Lt.length := List.length_filter_le _ _
      have h2 : Lh'.length ≤ Lh.length := List.length_filter_le _ _
      dsimp only [len', len]; omega
    have hLt'_mem : ∀ e, e ∈ Lt' ↔ e ∈ Lt ∧ e ∉ cs0.crossEdges := fun e => by
      simp only [Lt', List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨he, h0⟩
        refine ⟨he, fun hcr => ?_⟩
        rw [hcr_m e (hLt_lt e he), ite_eq_left hcr] at h0; omega
      · rintro ⟨he, hnc⟩
        refine ⟨he, ?_⟩
        rw [hcr_m e (hLt_lt e he), ite_eq_right hnc]
    have hLh'_mem : ∀ e, e ∈ Lh' ↔ e ∈ Lh ∧ e ∉ cs0.crossEdges := fun e => by
      simp only [Lh', List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨he, h0⟩
        refine ⟨he, fun hcr => ?_⟩
        rw [hcr_m e (hLh_lt e he), ite_eq_left hcr] at h0; omega
      · rintro ⟨he, hnc⟩
        refine ⟨he, ?_⟩
        rw [hcr_m e (hLh_lt e he), ite_eq_right hnc]
    have hB_end_lt : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ updBuf := by omega
    have hwin_B : CompDispatchWinOk W k b S x ec stB.mem :=
      hwin.of_agree
        ⟨hfrB _ (Or.inl (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffK] at hB_end_lt ⊢; omega)),
         hfrB _ (Or.inl (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffVCap] at hB_end_lt ⊢; omega)),
         hfrB _ (Or.inl (by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize, compOffHandlesPtr] at hB_end_lt ⊢; omega))⟩
        (fun j => hfrB _ (Or.inl (by
          have h1 : (ec.1 + 1) * k ≤ x.m0Total * k :=
            Nat.mul_le_mul_right k (Nat.succ_le_of_lt (lt_of_lt_of_le ec.2 hwin.2.2.1))
          have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
          dsimp only [compTablesEnd] at hB_end_lt; omega)))
        (fun j z hz => hfrB z (Or.inl (lt_of_lt_of_le hz.2 (le_trans (hwin.2.2.2.2.2.2.2.2.1 j).2.2.2.2.2.2 (by omega)))))
    have hUpdAt_B : UpdateAt stB.mem (updBuf + 1) ((S ⟨0, hwin_B.1⟩).compSt (x.compOf (x.edgefulComp ec))).G u_c len' := by
      rw [hcomp]
      rcases htag with rfl | rfl
      · exact projSplit_updateAt_tag2 hInv0 hT hvC (hLt_nd.filter _) (hLh_nd.filter _)
          hLt'_mem hLh'_mem (hLt_mem rfl) (hLh_mem rfl) hB_list
      · exact projSplit_updateAt_tag3 hInv0 hT hvC (hLt_nd.filter _) (hLh_nd.filter _)
          hLt'_mem hLh'_mem (hLt_mem3 rfl) (hLh_mem3 rfl) hB_list
    have hu_c_val : ((S ⟨0, hwin_B.1⟩).compSt (x.compOf (x.edgefulComp ec))).G.UpdateIsValid u_c := by
      rw [hcomp]
      have hpv := projCompUpdateG_valid hInv0 hu_valid_g (hT.compOf_mem cv)
      simp only [projCompUpdateG, hvC, ↓reduceIte, MGraph.BatchIsValid] at hpv
      exact hpv.1
    have hu_c_can : IsCanonUpd ((S ⟨0, hwin_B.1⟩).compSt (x.compOf (x.edgefulComp ec))).G u_c := by
      rw [hcomp]; refine ⟨fun e he => ?_, fun e he => ?_⟩
      · have := Finset.mem_filter.mp he; exact ⟨this.1, this.2.2.1⟩
      · have := Finset.mem_filter.mp he; exact ⟨this.1, this.2.2.1⟩
    have hwords_B : ∀ i < 1 + len', stB.mem (updBuf + i) < 2 ^ w := fun i hi => by
      rcases i with _ | i
      · rw [Nat.add_zero, hB_num]; omega
      · have hi' : i < ([tag, v, v', Lt'.length, Lh'.length] ++ Lt' ++ Lh').length := by simp; dsimp only [len'] at hi; omega
        have heq := hB_list i hi'
        rw [show updBuf + (i + 1) = updBuf + 1 + i by omega, heq]
        set z := ([tag, v, v', Lt'.length, Lh'.length] ++ Lt' ++ Lh')[i]
        have hmem : z ∈ [tag, v, v', Lt'.length, Lh'.length] ++ Lt' ++ Lh' := List.getElem_mem hi'
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with (((h | h | h | h | h) | hLt') | hLh')
        · rw [h]; rcases htag with rfl | rfl <;> exact lt_of_lt_of_le (by decide) hw16
        · rw [h]; have : x.vCap < 2 ^ w := by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hB_end_lt; omega
          omega
        · rw [h]; have : x.vCap < 2 ^ w := by dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hB_end_lt; omega
          omega
        · rw [h]; dsimp only [len'] at hlen'_le; dsimp only [len] at hlen'_le; omega
        · rw [h]; dsimp only [len'] at hlen'_le; dsimp only [len] at hlen'_le; omega
        · exact hLt_w z (List.mem_of_mem_filter hLt')
        · exact hLh_w z (List.mem_of_mem_filter hLh')
    let st2 : State := { stB with regs := Function.update stB.regs 24 ec.1 }
    have hs2 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 16) (.reg 12)))) stB .normal st2 5 := by
      rw [runs_assign_iff]; refine ⟨ec.1, ?_, rfl, rfl, by simp [Expr.size]⟩
      have hlt_buf : compEdgefulIdxBase b x.vCap + cv.1 < updBuf := by
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at hB_end_lt ⊢
        have := cv.2; omega
      simp [Expr.eval, BinOp.eval, hrB_lt19 16 (by omega), hrB_lt19 12 (by omega), st1, hr16, hr12,
        hefIdx_w, hfrB _ (Or.inl hlt_buf), hmi]
    obtain ⟨stD, cD, winConc_ec, cuts, hrunD, hbrD, hfrD, hzD, hcostD⟩ :=
      compDispatchOne_runs (p := p) (S := S) (x := x) (cnts := cnts) (mem := stB.mem) (pos := st2.pos) (ω := ω)
        hpZero hpLogAdd hpPreLog hpLsf hw16 ec hwin_B hend_le hcnt_buf (by dsimp only [len] at hlen'_le; omega)
        (fun z hz' => (hfrB z (Or.inr (by omega))).trans (hz z (by omega)))
        (fun j => (hfrB _ (Or.inl (by have := j.2; omega))).trans (hcnts_m j))
        (fun j => by
          have hGj := hwin.2.2.2.2.2.2.2.1 j; rw [hcomp] at hGj
          rw [hcomp]; have := hcap j; simpa [hGj, u_c, Gc, StC, ShC, cs0] using this)
        hB_num hwords_B hUpdAt_B hu_c_val hv'_lt hu_c_can
    let st3 : State := { st2 with regs := Function.update st2.regs 20 0, mem := stD.mem, pos := stD.pos }
    have hs3 : Runs w p ω (.call 20 bDisp [.reg 0, .reg 24, .reg 4, .reg 23, .reg 3]) st2 .normal st3 (cD + 6) := by
      rw [runs_call_iff]
      refine ⟨[b, ec.1, updBuf, 1 + len', cntBase], _, .returned 0, stD, cD, ?_, hpDisp, hrunD, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
      simp [evalArgs, Expr.eval, st2, hrB_lt19 0 (by omega), hrB_lt19 4 (by omega), hrB_lt19 3 (by omega),
        st1, hr0, hr4, hr3, hrB_23, len']
    have hthen : Runs w p ω _ st1 .normal st3 (cB + cD + 13) :=
      runs_seq_iff.mpr (Or.inr ⟨stB, cB, _, hrunB,
        runs_seq_iff.mpr (Or.inr ⟨st2, 5, cD + 6, hs2, hs3, rfl⟩), by omega⟩)
    have hcond : Runs w p ω (.cond (.reg 19) _ .nop) st1 .normal st3 (cB + cD + 15) :=
      runs_cond_iff.mpr ⟨1, cB + cD + 13, by simp [st1, Expr.eval, hef1], by simpa using hthen, by simp [Expr.size]; omega⟩
    have hrun_full : Runs w p ω (compStepSplitDispStmt bApp bDisp) st .normal st3 (cB + cD + 21) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, 5, cB + cD + 15, hs1, hcond, by omega⟩)
    let winConc' : Fin x.numEdgeful → Fin k → LSFConcrete := fun ec' j =>
      if ec' = ec then winConc_ec j else x.winConc ec' j
    have hphi_B : (∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) stB.mem) =
        ∑ j : Fin k, lsfPhi (x.winHandle ec j) (x.winConc ec j) st.mem :=
      Finset.sum_congr rfl fun j _ =>
        lsfPhi_congr fun z _ hz2 => hfrB z (Or.inl (lt_of_lt_of_le hz2 (le_trans (hwin.2.2.2.2.2.2.2.2.1 j).2.2.2.2.2.2 (by omega))))
    refine ⟨st3, cB + cD + 21, cuts, winConc', hrun_full,
      fun r hr => by simp [st3, st2, show r ≠ 20 by omega, show r ≠ 24 by omega, hrB_lt19 r hr, st1, show r ≠ 19 by omega],
      fun j => by
        obtain ⟨_, _, hcnt, hbuf, hval, hfe, hndE, hsE, hndR, hspR⟩ := hbrD j
        dsimp only [u_c] at hspR
        rw [hcomp] at hval hfe hsE hspR
        exact ⟨hcnt, hbuf, fun _ => ⟨hval, hfe, hndE, hsE, hndR, hspR⟩, fun hm => absurd hpos (by omega)⟩,
      fun ec' j => ⟨fun heq => by
        have heq_ec : ec' = ec := hefComp_inj ec' ec (heq.trans hcomp.symm)
        subst heq_ec; simp only [winConc', ↓reduceIte]
        exact ⟨(hbrD j).1, hcomp ▸ (hbrD j).2.1⟩,
        fun hne => by simp [winConc', show ec' ≠ ec from fun h => hne (h ▸ hcomp)]⟩,
      fun a hnw hnc hnrt hnfd hlt_buf =>
        (hfrD a (fun j => hnw ec j hcomp) hnc hnrt hnfd (Or.inl hlt_buf)).trans (hfrB a (Or.inl hlt_buf)),
      hzD, ?_⟩
    rw [dite_eq_left hpos]
    refine ⟨ec, hcomp, ?_⟩
    have hphi_new : (∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc' ec j) st3.mem) =
        ∑ j : Fin k, lsfPhi (x.winHandle ec j) (winConc_ec j) stD.mem :=
      Finset.sum_congr rfl fun j _ => by simp [winConc', st3]
    have hcost_mono : k * (lsfBatchCostFactor * ((1 + len') * x.L_w + 1) + 850) ≤
        k * (lsfBatchCostFactor * ((1 + len) * x.L_w + 1) + 850) :=
      Nat.mul_le_mul_left k (Nat.add_le_add_right
        (Nat.mul_le_mul_left lsfBatchCostFactor (Nat.add_le_add_right
          (Nat.mul_le_mul_right x.L_w (Nat.add_le_add_left hlen'_le 1)) 1)) 850)
    have hlen_eq : 5 + Lt.length + Lh.length = len := rfl
    rw [hlen_eq] at hcB
    rw [hphi_new]; rw [hphi_B] at hcostD; linarith
  · have hef0 : efFlag = 0 := ite_eq_right hpos
    have hcond : Runs w p ω (.cond (.reg 19)
        (compStepSplitBuildStmt bApp ;;
         .assign 24 (.load (.bin .add (.reg 16) (.reg 12))) ;;
         .call 20 bDisp [.reg 0, .reg 24, .reg 4, .reg 23, .reg 3]) .nop) st1 .normal st1 3 :=
      runs_cond_iff.mpr ⟨0, 1, by simp [st1, Expr.eval, hef0], by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
    have hrun_full : Runs w p ω (compStepSplitDispStmt bApp bDisp) st .normal st1 9 :=
      runs_seq_iff.mpr (Or.inr ⟨st1, 5, 3, hs1, hcond, rfl⟩)
    refine ⟨st1, 9, fun _ => [], x.winConc, hrun_full,
      fun r hr => by simp [st1, show r ≠ 19 by omega],
      fun j => ⟨by simpa using hcnts_m j, fun _ hi => by simp at hi,
        fun hp => absurd hp hpos, fun _ => rfl⟩,
      fun ec j => ⟨fun heq => absurd (heq ▸ hef_pos ec) hpos, fun _ => rfl⟩,
      fun _ _ _ _ _ _ => rfl, hz, ?_⟩
    rw [dite_eq_right hpos]; exact ⟨by omega, fun _ => rfl⟩

end

end MinCostFlow.SparseCore.Program
