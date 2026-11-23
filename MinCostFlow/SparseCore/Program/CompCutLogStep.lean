module

public import MinCostFlow.SparseCore.Program.CompCutLogBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pop-Step Verification for Forest-Cut Logging Root Closure (`CompCutLogStep`)

Proves `compLogPopStep_runs`, verifying one iteration of `compLogPopStepStmt`: cuts one
`π`-minimum edge, updates `fAnc` and `dgF`, relabels the smaller component, appends `(cutE, z)`
to `(fDelBuf, rootsBuf)`, and yields `155` steps of free amortized credit from the `lsfPhi` drop.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.DynSpanner.Program

@[expose] public section


/-! ## 1. Pop-step verification -/

set_option maxHeartbeats 600000 in
open Classical in
lemma compLogPopStep_runs {w b idxMinUp idxDgDel idxBFS rootsBuf fDelBuf cntPtr cap cnt : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete}
    {zIdx : ℕ} {rest : List ℕ} {st : State}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hbuf : CutLogBufOk w b (x.endAddr b) rootsBuf fDelBuf cntPtr cap)
    (hcnt_lt : cnt < cap) (hcnt_m : st.mem cntPtr = cnt)
    (hr40 : st.regs 40 = rootsBuf) (hr41 : st.regs 41 = fDelBuf) (hr42 : st.regs 42 = cntPtr)
    (hrep : (LSFRep x.h).rep b S x st.mem)
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDel : ∀ F, MeetsContract w p idxDgDel (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F))
    (hregs : PopRegsOk b x st.regs)
    (hr23 : st.regs 23 = rest.length + 1)
    (hlen_bd : rest.length + 1 ≤ hldDepthBound x.n0)
    (hstk : StackMemAt st.mem (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) (zIdx :: rest))
    (hThInv : ThStackInv S x.vList x.thParent x.n0 (zIdx :: rest)) :
    let z := x.vList[zIdx]!
    let S' : LSFState := { S with R₀_base := insert z S.R₀_base }
    ∃ st' c x' cutE,
      Runs w p ω (compLogPopStepStmt idxMinUp idxDgDel idxBFS) st .normal st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep x.h).rep b S' x' st'.mem ∧
      st'.mem cntPtr = cnt + 1 ∧
      st'.mem (rootsBuf + cnt) = z ∧
      st'.mem (fDelBuf + cnt) = cutE ∧
      (∀ a, (a < b ∨ x.endAddr b ≤ a) → a ≠ cntPtr → a ≠ rootsBuf + cnt → a ≠ fDelBuf + cnt →
        st'.mem a = st.mem a) ∧
      StackMemAt st'.mem (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) rest ∧
      PopRegsOk b x' st'.regs ∧
      st'.regs 23 = rest.length ∧
      st'.regs 40 = rootsBuf ∧ st'.regs 41 = fDelBuf ∧ st'.regs 42 = cntPtr ∧
      cutE ∈ S.RF.F.E ∧ z < x.vCap ∧ z ∈ S.RF.F.V ∧ z ∉ S.RF.R ∧
      (∀ v ∈ S.RF.F.V, ∃! rt, rt ∈ insert z S.RF.R ∧
        ({ S.RF.F with E := S.RF.F.E.erase cutE } : MGraph).Connected v rt) ∧
      compApplyForestCut S.RF (cutE, z) = S'.RF ∧
      c + 155 + lsfPhi b x' st'.mem ≤ lsfPhi b x st.mem := by
  intro z S'
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set eCapF := fECap eCap n0
  set tPtr := lsfTBlockPtr b vCap eCap
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set thStackBase := auxThStackBase auxPtr vCap n0
  have hlay := addRoot_layout hend_ltw
  have h_b_dgF : b + lsfHdrSize ≤ dgFPtr := by dsimp only [dgFPtr, vCap, eCap, tM]; omega
  have h_dgF_fAnc : dgFPtr + dynGraphSize vCap eCapF ≤ fAncPtr := by
    dsimp only [dgFPtr, fAncPtr, eCapF, vCap, eCap, n0, tM]; omega
  have h_fAnc_aux : fAncPtr + fAncSize vCap ≤ auxPtr := by
    dsimp only [fAncPtr, auxPtr, vCap, eCap, n0, tM, L_w]; omega
  have h_aux_end : auxPtr + auxSize vCap n0 ≤ x.endAddr b := by
    dsimp only [auxPtr, vCap, eCap, n0, tM, L_w]; omega
  have h_b_fAnc : b + lsfHdrSize ≤ fAncPtr := by clear * - h_b_dgF h_dgF_fAnc; omega
  have hrep_orig := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvT_lt, heG_lt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  rcases hThInv with ⟨hzIdx_lt, hz_not, hp_Rorig, hanc_iff, _⟩
  rcases hregs with ⟨hr0, hr2, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hr15,
    hr16, hr17, hr18, hr19, hr20, hr21, hr36, hr37⟩
  obtain ⟨hstk_top, hstk_rest⟩ := stackMemAt_tail hstk
  have hFAnc_copy := hFAnc; have hAux_copy := hAux; have hdgF_copy := hdgF
  rcases hAux with ⟨_, _, _, _, _, _, _, _, _, _, _, h11_qA, h12_qB, h13_vA, h14_vB, _, _,
    hvLen, hvNd, hvMem, htLen, hvLA, hvIdx, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hOrig_mem, hVis0⟩
  rcases hFAnc with ⟨hRcnt_mem, hIsR_ptr, hRL_ptr, hCid_ptr, hCR_ptr, hCS_ptr,
    _, hrL_len, _, _, _, hrL_at, hIsR_mem, hact_sub, hact_spec, hcid_mem⟩
  have hz_get : x.vList[zIdx]'(by omega) = z := (getElem!_pos x.vList zIdx (by omega)).symm
  have hzT : z ∈ S.T₀.V := hz_get ▸ (hvMem _).mp (List.getElem_mem _)
  have hz_vCap : z < vCap := hvT_lt z hzT
  have hz_F : z ∈ S.RF.F.V := hInv.RF_V_eq ▸ hInv.hGV_eq ▸ Finset.mem_union_left _ hzT
  obtain ⟨hold_eq, hold_act, hconn_zrC⟩ := hcid_mem z hz_F
  set oldCid := x.compId z
  rw [hold_eq] at hold_act hconn_zrC
  obtain ⟨hold_lt, hrC_mem, hrC_R, hcid_rC, holdSz_mem, holdSz_pos, holdSz_card⟩ := hact_spec oldCid hold_act
  set rC := x.compRoot oldCid
  set oldSize := x.compSize oldCid
  have hrC_F : rC ∈ S.RF.F.V := hInv.RF_V_eq ▸ hInv.to_RF_spanning.2.2.1 hrC_R
  have hrC_vCap : rC < vCap := hdgF.2.1 rC hrC_F
  have hstep := addOrigRoot_single_step hInv hzT hz_not hp_Rorig hanc_iff hrC_R hconn_zrC
  obtain ⟨hRorig', hz_not_R, hR', hInv', hrOrig_R, hz_ne_rOrig, hanc_or, hcut_mem, hF'_eq,
    haV, hbV, hnot_ab, hpart_V, hother_conn, hother_disj, hroots_sep⟩ := hstep
  set rOrig := S.origVert rC
  set cutE := minEdgeOn S.π (walkEdges (S.T₀.forestPath z rOrig))
  have htM_pos : 1 ≤ tM := by
    have hz_ne_r0 : z ≠ S.r₀ := fun h => hz_not (by change z ∈ S.R_orig; rw [h]; exact hInv.r₀_mem_R_orig)
    have hP := forestPath_isPath hInv.hT₀.isForest (hInv.hT₀.connected hzT hInv.hT₀.2)
    have hne : S.T₀.forestPath z S.r₀ ≠ [] := by
      intro h; rw [h] at hP
      have hnil_eq : ∀ {G : MGraph} {u v : ℕ}, G.IsWalk u v [] → u = v := fun hw => by cases hw; rfl
      exact hz_ne_r0 (hnil_eq hP.1)
    obtain ⟨e0, _, hEq⟩ := List.exists_cons_of_ne_nil hne
    have he0 : e0.1 ∈ S.T₀.E := by
      have hcons_mem : ∀ {G : MGraph} {u v : ℕ} {e : ℕ × Bool} {es : List (ℕ × Bool)},
          G.IsWalk u v (e :: es) → e.1 ∈ G.E := fun hw => by cases hw; assumption
      have hw := hP.1; rw [hEq] at hw; exact hcons_mem hw
    dsimp only [tM]; rw [← htM]; exact Finset.card_pos.mpr ⟨e0.1, he0⟩
  have hrOrig_T : rOrig ∈ S.T₀.V := hInv.R_orig_sub hrOrig_R
  have hrOrig_vCap : rOrig < vCap := hvT_lt rOrig hrOrig_T
  obtain ⟨rOrigIdx, hrOrigIdx_lt, hrOrig_get⟩ := List.mem_iff_getElem.mp ((hvMem rOrig).mpr hrOrig_T)
  have hrOrig_bang : x.vList[rOrigIdx]! = rOrig := by rw [getElem!_pos x.vList rOrigIdx hrOrigIdx_lt]; exact hrOrig_get
  have hvIdx_rOrig : st.mem (auxVIdxBase auxPtr + rOrig) = rOrigIdx + 1 := by
    have := hvIdx rOrigIdx hrOrigIdx_lt; rwa [hrOrig_get] at this
  have hne_idx : zIdx ≠ rOrigIdx := fun h => hz_ne_rOrig (by rw [← hrOrig_bang, ← h])
  set a := S.RF.F.tail cutE
  set b' := S.RF.F.head cutE
  have hcut_lt : cutE < eCapF := hdgF.2.2.1 cutE hcut_mem
  have ha_F : a ∈ S.RF.F.V := (hInv.to_RF_spanning.1.1 cutE hcut_mem).1
  have hb_F : b' ∈ S.RF.F.V := (hInv.to_RF_spanning.1.1 cutE hcut_mem).2
  have ha_vCap : a < vCap := hdgF.2.1 a ha_F
  have hb_vCap : b' < vCap := hdgF.2.1 b' hb_F
  have hEndSlot_cut := hdgF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cutE hcut_mem
  have hExtToInt_a := hdgF.2.2.2.2.2.2.2.2.2.1 a ha_F
  have hExtToInt_b := hdgF.2.2.2.2.2.2.2.2.2.1 b' hb_F
  have ha_read : st.mem (dgIntToExtBase dgFPtr vCap + st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE)) = a := by
    rw [hEndSlot_cut.1]; exact hExtToInt_a.2
  have hb_read : st.mem (dgIntToExtBase dgFPtr vCap + st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE)) = b' := by
    rw [hEndSlot_cut.2]; exact hExtToInt_b.2
  have hdgF_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w := by dsimp only [dgFPtr, eCapF, vCap, eCap, n0, tM]; omega
  have hfAnc_ltw : fAncPtr + fAncSize vCap < 2 ^ w := by dsimp only [fAncPtr, vCap, eCap, n0, tM]; omega
  have haux_ltw : auxPtr + auxSize vCap n0 < 2 ^ w := by dsimp only [auxPtr, vCap, eCap, n0, tM, L_w]; omega
  have ht_ltw : tPtr + tBlockSize vCap eCap tM < 2 ^ w := by dsimp only [tPtr, vCap, eCap, tM]; omega
  have hdgF_sz : dynGraphSize vCap eCapF = 4 + 7 * vCap + 9 * eCapF := rfl
  have hfAnc_sz : fAncSize vCap = 6 + 5 * vCap := rfl
  have hvCap_ltw : vCap < 2 ^ w := by omega
  have holdSz_le : oldSize ≤ vCap := by
    rw [holdSz_card]
    have hsub : (S.RF.F.V.filter fun u => S.RF.F.Connected u rC) ⊆ Finset.range vCap :=
      fun u hu => Finset.mem_range.mpr (hdgF.2.1 u (Finset.mem_filter.mp hu).1)
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_range vCap)
  have hrCnt_lt : S.RF.R.card < vCap := by
    have hsub : insert z S.RF.R ⊆ Finset.range vCap := fun v hv => by
      rw [Finset.mem_insert] at hv; rcases hv with rfl | hvR
      · exact Finset.mem_range.mpr hz_vCap
      · exact Finset.mem_range.mpr (hdgF.2.1 v (hInv.RF_V_eq ▸ hInv.to_RF_spanning.2.2.1 hvR))
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_range vCap)
    have hz_not_RF : z ∉ S.RF.R := hz_not_R
    rw [Finset.card_insert_of_notMem hz_not_RF] at hc; omega
  have haux_vList_ltw : auxVListBase auxPtr vCap + zIdx < 2 ^ w := by
    dsimp [auxVListBase, auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  have haux_orig_ltw : auxOrigVertBase auxPtr vCap n0 + rC < 2 ^ w := by
    dsimp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  have haux_vIdx_ltw : auxVIdxBase auxPtr + rOrig < 2 ^ w := by dsimp [auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  have hcid_z_ltw : fCompIdBase fAncPtr vCap + z < 2 ^ w := by dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]; omega
  have hcr_old_ltw : fCompRootBase fAncPtr vCap + oldCid < 2 ^ w := by
    dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]; omega
  have hcs_old_ltw : fCompSizeBase fAncPtr vCap + oldCid < 2 ^ w := by
    dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize]; omega
  have hisr_z_ltw : fIsRootBase fAncPtr + z < 2 ^ w := by dsimp [fIsRootBase, fAncHdrSize]; omega
  have hrL_cnt_ltw : fRListBase fAncPtr vCap + S.RF.R.card < 2 ^ w := by dsimp [fRListBase, fIsRootBase, fAncHdrSize]; omega
  have hf_rcnt_ltw : fAncPtr + fOffRCount < 2 ^ w := by dsimp [fOffRCount]; omega
  have hb_rcnt_ltw : b + lsfOffRCount < 2 ^ w := by dsimp [lsfOffRCount, lsfHdrSize] at hlay ⊢; omega
  have h24_ltw : 24 < 2 ^ w := by dsimp only [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfHdrSize] at hend_ltw; omega
  have hrcnt1_ltw : S.RF.R.card + 1 < 2 ^ w := by clear * - hrCnt_lt hvCap_ltw; omega
  have hstk_r_ltw : thStackBase + rest.length < 2 ^ w := by
    dsimp [thStackBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      auxSize] at haux_ltw ⊢; omega
  have hETail_ltw : dgETailSlotBase dgFPtr vCap eCapF + cutE < 2 ^ w := by dsimp [dgETailSlotBase]; omega
  have hEHead_ltw : dgEHeadSlotBase dgFPtr vCap eCapF + cutE < 2 ^ w := by dsimp [dgEHeadSlotBase]; omega
  have ha_slot_lt : st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE) < vCap :=
    hEndSlot_cut.1.symm ▸ hdgF.2.1 _ hExtToInt_a.1
  have hb_slot_lt : st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE) < vCap :=
    hEndSlot_cut.2.symm ▸ hdgF.2.1 _ hExtToInt_b.1
  have hIntA_ltw : dgIntToExtBase dgFPtr vCap + st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE) < 2 ^ w := by
    dsimp [dgIntToExtBase]; omega
  have hIntB_ltw : dgIntToExtBase dgFPtr vCap + st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE) < 2 ^ w := by
    dsimp [dgIntToExtBase]; omega
  set mSmall := min (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a).card
                    (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b').card
  have hrun_goal : ∃ o st' c,
      Runs w p ω (compLogPopStepStmt idxMinUp idxDgDel idxBFS) st o st' c ∧
      (o = .normal ∧ ∃ x',
        SameStaticConcrete x x' ∧
        (LSFRep x.h).rep b S' x' st'.mem ∧
        st'.mem cntPtr = cnt + 1 ∧
        st'.mem (rootsBuf + cnt) = z ∧
        st'.mem (fDelBuf + cnt) = cutE ∧
        (∀ a_addr, (a_addr < b ∨ x.endAddr b ≤ a_addr) →
          a_addr ≠ cntPtr → a_addr ≠ rootsBuf + cnt → a_addr ≠ fDelBuf + cnt →
          st'.mem a_addr = st.mem a_addr) ∧
        StackMemAt st'.mem thStackBase rest ∧
        PopRegsOk b x' st'.regs ∧
        st'.regs 23 = rest.length ∧
        st'.regs 40 = rootsBuf ∧ st'.regs 41 = fDelBuf ∧ st'.regs 42 = cntPtr ∧
        lsfPhi b x' st'.mem + 500 * auxLogCap n0 + 1400 + 1100 * mSmall ≤ lsfPhi b x st.mem) ∧
      c ≤ 120 * auxLogCap n0 + 600 * mSmall + 1490 := by
    dsimp only [compLogPopStepStmt]
    refine runs_start_le ?_
    refine addOrigRootPopRead_seq_le hw16 (by omega) (by omega) hstk_r_ltw haux_vList_ltw
      hcid_z_ltw hcr_old_ltw hcs_old_ltw haux_orig_ltw haux_vIdx_ltw
      hr11 hr12 hr14 hr15 hr17 hr18 hr19 hr23 hstk_top
      (by rw [← hz_get]; exact hvLA zIdx (by omega)) hold_eq hrC_mem holdSz_mem
      (hOrig_mem rC (hInv.RF_V_eq ▸ hrC_F) hrC_vCap) hvIdx_rOrig ?_
    have hpre_min : (minEdgeUpContract w S x.vList x.tOrigList).pre
        [auxPtr, tPtr, vCap, n0, tM, zIdx, rOrigIdx] st.mem :=
      ⟨auxPtr, tPtr, vCap, eCap, n0, tM, zIdx, rOrigIdx,
        x.t0Parent, x.t0ParentTreeIdx, x.t0Depth, x.thParent, x.upV, x.upMinIdx,
        rfl, hw16, haux_ltw, ht_ltw, hInv, htM_pos, hAux_copy, hT,
        hzIdx_lt, by omega, hne_idx, by rw [hrOrig_bang]; exact hanc_or⟩
    have hpre_del : (dgDeleteEdgeContract w vCap eCapF S.RF.F).pre [dgFPtr, cutE] st.mem :=
      ⟨dgFPtr, cutE, rfl, hw16, hdgF_ltw, hdgF_copy⟩
    refine compLogPopCut_seq_le hw16 h24_ltw h_dgF_fAnc haux_ltw (by omega) hdgF_ltw
      hvCap_ltw hnv htn hzIdx_lt (by omega) hcut_lt hETail_ltw hEHead_ltw hIntA_ltw hIntB_ltw
      hisr_z_ltw hf_rcnt_ltw hrL_cnt_ltw hb_rcnt_ltw hrcnt1_ltw
      hr0 hr2 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr16 hr21 hr36 hr37
      ha_read hb_read hRcnt_mem (by rw [hrOrig_bang])
      (hMinUp S) hpre_min (hDgDel S.RF.F) hpre_del ?_
    intro mem1 pos1 regs2 hdgF1_raw hfr1 hreg2_lo hr2_23 hr2_25 hr2_26 hr2_27 hr2_28 hr2_31 hr2_32 hr2_33
    have hdgF1 : DynGraphAt mem1 dgFPtr vCap eCapF S'.RF.F := by
      rw [ite_eq_left hcut_mem] at hdgF1_raw
      have hsub : S.RF.F.applyUpdate (.delete cutE) = S'.RF.F := hF'_eq.symm
      rw [← hsub]; exact hdgF1_raw
    have hmem1_fAnc : ∀ a_addr, fAncPtr ≤ a_addr → mem1 a_addr = st.mem a_addr :=
      fun a_addr ha => hfr1 a_addr (Or.inr (by clear * - h_dgF_fAnc ha; omega))
    let mem2 : ℕ → ℕ := Function.update
      (Function.update
        (Function.update
          (Function.update mem1 (fIsRootBase fAncPtr + z) 1)
          (fRListBase fAncPtr vCap + S.RF.R.card) z)
        (fAncPtr + fOffRCount) (S.RF.R.card + 1))
      (b + lsfOffRCount) (S.RF.R.card + 1)
    have hmem2_eq : ∀ a_addr,
        a_addr ≠ b + lsfOffRCount → a_addr ≠ fAncPtr + fOffRCount →
        a_addr ≠ fRListBase fAncPtr vCap + S.RF.R.card → a_addr ≠ fIsRootBase fAncPtr + z →
        mem2 a_addr = mem1 a_addr := fun a_addr h1 h2 h3 h4 => by
      dsimp only [mem2]
      rw [Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, Function.update_of_ne h4]
    have hdgF2 : DynGraphAt mem2 dgFPtr vCap eCapF S'.RF.F :=
      hdgF1.of_agree fun a_addr ha1 ha2 => hmem2_eq a_addr
        (by clear * - h_b_dgF ha1; dsimp [lsfOffRCount, lsfHdrSize] at h_b_dgF ⊢; omega)
        (by clear * - h_dgF_fAnc ha2; dsimp [fOffRCount]; omega)
        (by clear * - h_dgF_fAnc ha2; dsimp [fRListBase, fIsRootBase]; omega)
        (by clear * - h_dgF_fAnc ha2; dsimp [fIsRootBase]; omega)
    have hmem2_ge_cid : ∀ a_addr, fCompIdBase fAncPtr vCap ≤ a_addr → mem2 a_addr = st.mem a_addr :=
      fun a_addr ha => (hmem2_eq a_addr
        (by clear * - h_b_fAnc ha; dsimp [fCompIdBase, fRListBase, fIsRootBase, lsfOffRCount, lsfHdrSize] at h_b_fAnc ha ⊢; omega)
        (by clear * - ha; dsimp [fCompIdBase, fRListBase, fIsRootBase, fOffRCount, fAncHdrSize] at ha ⊢; omega)
        (by clear * - hrCnt_lt ha; dsimp [fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega)
        (by clear * - hz_vCap ha; dsimp [fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega)).trans
        (hmem1_fAnc a_addr (by clear * - ha; dsimp [fCompIdBase, fRListBase, fIsRootBase] at ha ⊢; omega))
    have hmem2_aux : ∀ a_addr, auxPtr ≤ a_addr → mem2 a_addr = st.mem a_addr := fun a_addr ha =>
      hmem2_ge_cid a_addr (by clear * - h_fAnc_aux ha; dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize] at h_fAnc_aux ha ⊢; omega)
    have hmem2_fHdr : ∀ off, 1 ≤ off → off < fAncHdrSize → mem2 (fAncPtr + off) = st.mem (fAncPtr + off) :=
      fun off ho1 ho2 => (hmem2_eq _
        (by clear * - h_b_fAnc; dsimp [lsfOffRCount, lsfHdrSize] at h_b_fAnc ⊢; omega)
        (by clear * - ho1; dsimp [fOffRCount]; omega)
        (by clear * - ho2; dsimp [fRListBase, fIsRootBase, fAncHdrSize] at ho2 ⊢; omega)
        (by clear * - ho2; dsimp [fIsRootBase, fAncHdrSize] at ho2 ⊢; omega)).trans
        (hmem1_fAnc _ (Nat.le_add_right _ _))
    have hnewSum_eq : oldSize =
        (S'.RF.F.V.filter fun v => S'.RF.F.Connected v a).card +
        (S'.RF.F.V.filter fun v => S'.RF.F.Connected v b').card := by
      have hdisj_ab : Disjoint (S'.RF.F.V.filter fun v => S'.RF.F.Connected v a)
          (S'.RF.F.V.filter fun v => S'.RF.F.Connected v b') := by
        rw [Finset.disjoint_left]; intro v hv1 hv2
        exact hnot_ab (connected_trans (connected_symm (Finset.mem_filter.mp hv1).2)
          (Finset.mem_filter.mp hv2).2)
      rw [← Finset.card_union_of_disjoint hdisj_ab, holdSz_card]
      congr 1; ext v; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ⟨hvF, hvr⟩
        have hvF' : v ∈ S'.RF.F.V := by rw [hF'_eq]; exact hvF
        rcases (hpart_V v hvF').mpr (Or.inr ⟨hvF, hvr⟩) with h1 | h2
        · exact Or.inl ⟨hvF', h1⟩
        · exact Or.inr ⟨hvF', h2⟩
      · rintro (⟨hvF', h1⟩ | ⟨hvF', h2⟩)
        · rcases (hpart_V v hvF').mp (Or.inl h1) with rfl | h
          · exact ⟨hz_F, hconn_zrC⟩
          · exact h
        · rcases (hpart_V v hvF').mp (Or.inr h2) with rfl | h
          · exact ⟨hz_F, hconn_zrC⟩
          · exact h
    have hold_ne_z : oldCid ≠ z := fun h => hz_not_R (h ▸ hact_sub hold_act)
    have hpre_bfs : (splitCompBFSContract w S'.RF.F).pre
        [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, a, b', oldCid, rC, z, oldSize] mem2 :=
      ⟨dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, a, b', oldCid, rC, z, oldSize,
        rfl, hw16,
        (by dsimp only [dgFPtr, fAncPtr, eCapF, vCap, eCap, n0, tM]; omega),
        (by dsimp only [fAncPtr, auxPtr, vCap, eCap, n0, tM, L_w]; omega),
        haux_ltw, hInv'.to_RF_spanning.1, hdgF2,
        (hmem2_fHdr fOffCompIdPtr (by decide) (by decide)).trans hCid_ptr,
        (hmem2_fHdr fOffCompRootPtr (by decide) (by decide)).trans hCR_ptr,
        (hmem2_fHdr fOffCompSizePtr (by decide) (by decide)).trans hCS_ptr,
        (hmem2_aux _ (Nat.le_add_right _ _)).trans h11_qA,
        (hmem2_aux _ (Nat.le_add_right _ _)).trans h12_qB,
        (hmem2_aux _ (Nat.le_add_right _ _)).trans h13_vA,
        (hmem2_aux _ (Nat.le_add_right _ _)).trans h14_vB,
        fun v hv => ⟨(hmem2_aux _ (by dsimp [auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hVis0 v hv).1,
          (hmem2_aux _ (by dsimp [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
          auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
          auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)).trans (hVis0 v hv).2⟩,
        haV, hbV, hnot_ab, hold_lt, hrC_vCap, hz_vCap, hold_ne_z, hroots_sep, hnewSum_eq⟩
    have hargs_bfs : evalArgs w { mem := mem2, regs := regs2, pos := pos1 }
        [.reg 7, .reg 8, .reg 9, .reg 2, .reg 20, .reg 4,
         .reg 32, .reg 33, .reg 26, .reg 27, .reg 25, .reg 28] =
        some [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, a, b', oldCid, rC, z, oldSize] := by
      change some [regs2 7, regs2 8, regs2 9, regs2 2, regs2 20, regs2 4,
        regs2 32, regs2 33, regs2 26, regs2 27, regs2 25, regs2 28] = _
      rw [hreg2_lo 7 (by decide), hr7, hreg2_lo 8 (by decide), hr8, hreg2_lo 9 (by decide), hr9,
        hreg2_lo 2 (by decide), hr2, hreg2_lo 20 (by decide), hr20, hreg2_lo 4 (by decide), hr4,
        hr2_32, hr2_33, hr2_26, hr2_27, hr2_25, hr2_28]
    have hvals_bfs : ∀ v ∈ [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, a, b', oldCid, rC, z, oldSize],
        v < 2 ^ w := by
      intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      have hn0_lt : n0 ≤ vCap := hnv
      clear * - hv hdgF_ltw hdgF_sz hfAnc_ltw haux_ltw hvCap_ltw hn0_lt
        ha_vCap hb_vCap hold_lt hrC_vCap hz_vCap holdSz_le
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine runs_seq_call_le (hBFS S'.RF.F) hargs_bfs hvals_bfs hpre_bfs ?_
    intro v_bfs mem3 pos3 hpost_bfs
    have hv_bfs0 : v_bfs = 0 := by
      rcases hpost_bfs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hv0, _⟩; exact hv0
    subst hv_bfs0
    obtain ⟨x', hsame, hrep3, hmem3_out, hstk3, hphi_drop⟩ :=
      addOrigRootPopStep_post hend_ltw hrep_orig hzIdx_lt hz_not hold_eq rfl hold_act rfl rfl
        hconn_zrC hRorig' hz_not_R hR' hInv' hcut_mem hF'_eq rfl rfl haV hbV hnot_ab
        hpart_V hother_conn hother_disj hroots_sep hstk_rest hdgF1 hfr1 rfl hnewSum_eq hpost_bfs
    -- Execute the 4 logging instructions on `mem3`
    have hcnt_m3 : mem3 cntPtr = cnt := (hmem3_out cntPtr hbuf.1).trans hcnt_m
    have hrb_w : rootsBuf + cnt < 2 ^ w := by rcases hbuf with ⟨_, _, _, _, _, _, h1, _, _, _⟩; omega
    have hfb_w : fDelBuf + cnt < 2 ^ w := by rcases hbuf with ⟨_, _, _, _, _, _, _, h1, _, _⟩; omega
    have hcnt1_w : cnt + 1 < 2 ^ w := by rcases hbuf with ⟨_, _, _, _, _, _, _, _, _, h1⟩; omega
    have h1_w : (1 : ℕ) < 2 ^ w := by omega
    have hr2_40 : regs2 40 = rootsBuf := (hreg2_lo 40 (by decide)).trans hr40
    have hr2_41 : regs2 41 = fDelBuf := (hreg2_lo 41 (by decide)).trans hr41
    have hr2_42 : regs2 42 = cntPtr := (hreg2_lo 42 (by decide)).trans hr42
    refine runs_seq_assign_le (v := cnt) (Expr.eval_load_of_eq (by simp [Expr.eval, hr2_42]) hcnt_m3) ?_; dsimp only
    refine runs_seq_store_le (x := rootsBuf + cnt) (v := z)
      (by simp [Expr.eval, BinOp.eval, hr2_40, hrb_w])
      (by simp [Expr.eval, hr2_25]) ?_; dsimp only
    refine runs_seq_store_le (x := fDelBuf + cnt) (v := cutE)
      (by simp [Expr.eval, BinOp.eval, hr2_41, hfb_w])
      (by simp [Expr.eval, hr2_31]) ?_; dsimp only
    refine runs_store_le (x := cntPtr) (v := cnt + 1)
      (by simp [Expr.eval, hr2_42])
      (by simp [Expr.eval, BinOp.eval, h1_w, hcnt1_w]) ?_ ?_
    · set mem4 := Function.update (Function.update (Function.update mem3 (rootsBuf + cnt) z)
        (fDelBuf + cnt) cutE) cntPtr (cnt + 1)
      have hne_c_f : cntPtr ≠ fDelBuf + cnt := by rcases hbuf with ⟨_, _, _, _, _, h, _⟩; omega
      have hne_c_r : cntPtr ≠ rootsBuf + cnt := by rcases hbuf with ⟨_, _, _, _, h, _⟩; omega
      have hne_f_r : fDelBuf + cnt ≠ rootsBuf + cnt := by rcases hbuf with ⟨_, _, _, h, _⟩; omega
      have hwin_eq : ∀ a_addr, b ≤ a_addr → a_addr < x.endAddr b → mem4 a_addr = mem3 a_addr := fun a_addr ha1 ha2 => by
        dsimp only [mem4]; rcases hbuf with ⟨h1, h2, h3, _⟩
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
      have hend_eq : x'.endAddr b = x.endAddr b := hsame.endAddr b
      have hrep4 : (LSFRep x.h).rep b S' x' mem4 :=
        (lsfRep_local x.h b S' x' mem3 mem4 fun a_addr ha =>
          (hwin_eq a_addr ha.1 (hend_eq ▸ ha.2)).symm).1 hrep3
      have hphi4 : lsfPhi b x' mem4 = lsfPhi b x' mem3 :=
        lsfPhi_congr fun a_addr ha1 ha2 => hwin_eq a_addr ha1 (hend_eq ▸ ha2)
      have hstk4 : StackMemAt mem4 thStackBase rest := by
        intro i hi
        have hlt : thStackBase + (rest.length - 1 - i) < x.endAddr b := by
          dsimp [thStackBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
            auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
            auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
            auxSize] at h_aux_end ⊢; omega
        have hge : b ≤ thStackBase + (rest.length - 1 - i) := by
          dsimp [thStackBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
            auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
            auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega
        exact (hwin_eq _ hge hlt).trans (hstk3 i hi)
      have hreg_kept : ∀ r, r ≤ 21 ∨ r = 36 ∨ r = 37 →
          Function.update (Function.update regs2 34 0) 43 cnt r = st.regs r := fun r hr => by
        rw [Function.update_of_ne (by clear * - hr; omega), Function.update_of_ne (by clear * - hr; omega)]
        exact hreg2_lo r (by clear * - hr; omega)
      have hPopRegs4 : PopRegsOk b x' (Function.update (Function.update regs2 34 0) 43 cnt) := by
        dsimp only [PopRegsOk]
        rw [hsame.1, hsame.2.1, hsame.2.2.1, hsame.2.2.2.2.1, hsame.2.2.2.2.2.2.2.2.1]
        exact ⟨(hreg_kept 0 (by omega)).trans hr0, (hreg_kept 2 (by omega)).trans hr2,
          (hreg_kept 4 (by omega)).trans hr4, (hreg_kept 5 (by omega)).trans hr5,
          (hreg_kept 6 (by omega)).trans hr6, (hreg_kept 7 (by omega)).trans hr7,
          (hreg_kept 8 (by omega)).trans hr8, (hreg_kept 9 (by omega)).trans hr9,
          (hreg_kept 10 (by omega)).trans hr10, (hreg_kept 11 (by omega)).trans hr11,
          (hreg_kept 12 (by omega)).trans hr12, (hreg_kept 14 (by omega)).trans hr14,
          (hreg_kept 15 (by omega)).trans hr15, (hreg_kept 16 (by omega)).trans hr16,
          (hreg_kept 17 (by omega)).trans hr17, (hreg_kept 18 (by omega)).trans hr18,
          (hreg_kept 19 (by omega)).trans hr19, (hreg_kept 20 (by omega)).trans hr20,
          (hreg_kept 21 (by omega)).trans hr21, (hreg_kept 36 (by omega)).trans hr36,
          (hreg_kept 37 (by omega)).trans hr37⟩
      refine ⟨rfl, x', hsame, hrep4, Function.update_self _ _ _, ?_, ?_, ?_, hstk4, hPopRegs4,
        by simp [hr2_23], by simp [hr2_40], by simp [hr2_41], by simp [hr2_42],
        by rw [hphi4]; exact hphi_drop⟩
      · dsimp only [mem4]; rw [Function.update_of_ne hne_c_r.symm, Function.update_of_ne hne_f_r.symm, Function.update_self]
      · dsimp only [mem4]; rw [Function.update_of_ne hne_c_f.symm, Function.update_self]
      · intro a_addr ha h1 h2 h3
        dsimp only [mem4]
        rw [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h2]
        exact hmem3_out a_addr ha
    · have hcost_bfs : (splitCompBFSContract w S'.RF.F).cost
          [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, a, b', oldCid, rC, z, oldSize] mem2 =
          600 * mSmall + 700 := rfl
      rw [hcost_bfs]
      have hs1 : argsSize [.reg 7, .reg 8, .reg 9, .reg 2, .reg 20, .reg 4,
          .reg 32, .reg 33, .reg 26, .reg 27, .reg 25, .reg 28] = 12 := rfl
      have hs2 : (Expr.load (.reg 42)).size = 2 := rfl
      have hs3 : (Expr.bin .add (.reg 40) (.reg 43)).size = 3 := rfl
      have hs4 : (Expr.bin .add (.reg 41) (.reg 43)).size = 3 := rfl
      have hs5 : (Expr.bin .add (.reg 43) (.const 1)).size = 3 := rfl
      have hs6 : (Expr.reg 25).size = 1 := rfl
      have hs7 : (Expr.reg 31).size = 1 := rfl
      have hs8 : (Expr.reg 42).size = 1 := rfl
      rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8]
      clear * -; omega
  obtain ⟨o, st', c, hrun, ⟨rfl, x', hsame, hrep', hcm, hrm, hfm, hfr', hstk', hregs', hr23',
    hr40', hr41', hr42', hphi_d⟩, hc⟩ := hrun_goal
  have hlog1 : 1 ≤ auxLogCap n0 := by dsimp [auxLogCap]; omega
  have hcm_bd : c + 155 ≤ 500 * auxLogCap n0 + 1400 + 1100 * mSmall := by
    have : 120 * auxLogCap n0 + 600 * mSmall + 1490 + 155 ≤
        500 * auxLogCap n0 + 1400 + 1100 * mSmall := by clear * - hlog1; omega
    exact Nat.le_trans (Nat.add_le_add_right hc 155) this
  have hRF_eq : compApplyForestCut S.RF (cutE, z) = S'.RF := by
    cases hRF : S'.RF with
    | mk F' R' =>
      have hFeq : F' = { S.RF.F with E := S.RF.F.E.erase cutE } := by
        have := hF'_eq; rw [hRF] at this; exact this
      have hReq : R' = insert z S.RF.R := by
        have := hR'; change S'.RF.R = insert z S.RF.R at this; rw [hRF] at this; exact this
      simp [compApplyForestCut, hFeq, hReq]
  have huniq : ∀ v ∈ S.RF.F.V, ∃! rt, rt ∈ insert z S.RF.R ∧
      ({ S.RF.F with E := S.RF.F.E.erase cutE } : MGraph).Connected v rt := by
    intro v hv
    have hv' : v ∈ S'.RF.F.V := by rw [hF'_eq]; exact hv
    have hu := hInv'.to_RF_spanning.2.2.2.1 v (hInv'.RF_V_eq.symm ▸ hv')
    rwa [← hRF_eq] at hu
  refine ⟨st', c, x', cutE, hrun, hsame, hrep', hcm, hrm, hfm, hfr', hstk', hregs', hr23',
    hr40', hr41', hr42', hcut_mem, hz_vCap, hz_F, hz_not_R, huniq, hRF_eq, ?_⟩
  calc c + 155 + lsfPhi b x' st'.mem
      = lsfPhi b x' st'.mem + (c + 155) := Nat.add_comm _ _
    _ ≤ lsfPhi b x' st'.mem + (500 * auxLogCap n0 + 1400 + 1100 * mSmall) := Nat.add_le_add_left hcm_bd _
    _ = lsfPhi b x' st'.mem + 500 * auxLogCap n0 + 1400 + 1100 * mSmall := by ring
    _ ≤ lsfPhi b x st.mem := hphi_d


end

end MinCostFlow.SparseCore.Program
