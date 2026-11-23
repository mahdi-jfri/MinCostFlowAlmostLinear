module

public import MinCostFlow.LSF.Program.BatchAddRootPost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Root-Closure Pop Loop and Top-Level Verification (`BatchAddRoot`)

Verifies the LIFO pop step (`addOrigRootPopStep_runs`), pop loop (`addOrigRootPopLoop_runs`), and
full amortized top-level execution of `addOrigRootProc` (`addOrigRoot_runs`,
`addOrigRoot_call_runs`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

open Classical in
/-- Verification of one iteration of `addOrigRootPopStepStmt`: pops `zIdx`, cuts `cutE`, updates
`fAnc` and `b.rCount`, relabels the smaller component, preserves `LSFRep`, and pays `c + 40` from
the drop in `lsfPhi`. -/
private lemma addOrigRootPopStep_runs {w b idxMinUp idxDgDel idxBFS : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete}
    {zIdx : ℕ} {rest : List ℕ} {st : State}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
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
    ∃ st' c x',
      Runs w p ω (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) st .normal st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep x.h).rep b S' x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = st.mem a) ∧
      StackMemAt st'.mem (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) rest ∧
      PopRegsOk b x' st'.regs ∧
      st'.regs 23 = rest.length ∧
      c + 40 + lsfPhi b x' st'.mem ≤ lsfPhi b x st.mem := by
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
  have h_fAnc_end : fCompSizeBase fAncPtr vCap + vCap = fAncPtr + fAncSize vCap :=
    fAnc_end_eq fAncPtr vCap
  have h_qB_aux : auxQBufBBase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
    clear * - vCap; dsimp [auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase,
      auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
      auxVListBase, auxVIdxBase, auxSize]; omega
  have h_aux_qA : auxPtr ≤ auxQBufABase auxPtr vCap n0 := by
    clear * - vCap; dsimp [auxQBufABase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
      auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase,
      auxVIdxBase]; omega
  have hrep_orig := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvT_lt, heG_lt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  rcases hThInv with ⟨hzIdx_lt, hz_not, hp_Rorig, hanc_iff, _⟩
  rcases hregs with ⟨hr0, hr2, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr14, hr15,
    hr16, hr17, hr18, hr19, hr20, hr21, hr36, hr37⟩
  obtain ⟨hstk_top, hstk_rest⟩ := stackMemAt_tail hstk
  have hFAnc_copy := hFAnc
  have hAux_copy := hAux
  have hdgF_copy := hdgF
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
  have hrOrig_bang : x.vList[rOrigIdx]! = rOrig := by
    rw [getElem!_pos x.vList rOrigIdx hrOrigIdx_lt]; exact hrOrig_get
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
  have ha_slot_lt : st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE) < vCap :=
    hEndSlot_cut.1.symm ▸ hdgF.2.1 _ hExtToInt_a.1
  have hb_slot_lt : st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE) < vCap :=
    hEndSlot_cut.2.symm ▸ hdgF.2.1 _ hExtToInt_b.1
  have ha_read : st.mem (dgIntToExtBase dgFPtr vCap + st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE)) = a := by
    rw [hEndSlot_cut.1]; exact hExtToInt_a.2
  have hb_read : st.mem (dgIntToExtBase dgFPtr vCap + st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE)) = b' := by
    rw [hEndSlot_cut.2]; exact hExtToInt_b.2
  have hdgF_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w := by
    dsimp only [dgFPtr, eCapF, vCap, eCap, n0, tM]; omega
  have hfAnc_ltw : fAncPtr + fAncSize vCap < 2 ^ w := by
    dsimp only [fAncPtr, vCap, eCap, n0, tM]; omega
  have haux_ltw : auxPtr + auxSize vCap n0 < 2 ^ w := by
    dsimp only [auxPtr, vCap, eCap, n0, tM, L_w]; omega
  have ht_ltw : tPtr + tBlockSize vCap eCap tM < 2 ^ w := by
    dsimp only [tPtr, vCap, eCap, tM]; omega
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
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hvR
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
  have haux_vIdx_ltw : auxVIdxBase auxPtr + rOrig < 2 ^ w := by
    dsimp [auxVIdxBase, auxSize] at haux_ltw ⊢; omega
  have hcid_z_ltw : fCompIdBase fAncPtr vCap + z < 2 ^ w := by
    dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize] at ⊢; omega
  have hcr_old_ltw : fCompRootBase fAncPtr vCap + oldCid < 2 ^ w := by
    dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize] at ⊢; omega
  have hcs_old_ltw : fCompSizeBase fAncPtr vCap + oldCid < 2 ^ w := by
    dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncHdrSize] at ⊢; omega
  have hisr_z_ltw : fIsRootBase fAncPtr + z < 2 ^ w := by dsimp [fIsRootBase, fAncHdrSize]; omega
  have hrL_cnt_ltw : fRListBase fAncPtr vCap + S.RF.R.card < 2 ^ w := by
    dsimp [fRListBase, fIsRootBase, fAncHdrSize]; omega
  have hf_rcnt_ltw : fAncPtr + fOffRCount < 2 ^ w := by dsimp [fOffRCount]; omega
  have hb_rcnt_ltw : b + lsfOffRCount < 2 ^ w := by dsimp [lsfOffRCount, lsfHdrSize] at hlay ⊢; omega
  have h24_ltw : 24 < 2 ^ w := by
    dsimp only [LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfHdrSize] at hend_ltw; omega
  have hrcnt1_ltw : S.RF.R.card + 1 < 2 ^ w := by clear * - hrCnt_lt hvCap_ltw; omega
  have hstk_r_ltw : thStackBase + rest.length < 2 ^ w := by
    dsimp [thStackBase, auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
      auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      auxSize] at haux_ltw ⊢; omega
  have hETail_ltw : dgETailSlotBase dgFPtr vCap eCapF + cutE < 2 ^ w := by
    dsimp [dgETailSlotBase]; omega
  have hEHead_ltw : dgEHeadSlotBase dgFPtr vCap eCapF + cutE < 2 ^ w := by
    dsimp [dgEHeadSlotBase]; omega
  have hIntA_ltw : dgIntToExtBase dgFPtr vCap + st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE) < 2 ^ w := by
    dsimp [dgIntToExtBase]; omega
  have hIntB_ltw : dgIntToExtBase dgFPtr vCap + st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE) < 2 ^ w := by
    dsimp [dgIntToExtBase]; omega
  set mSmall := min (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) a).card
                    (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) b').card
  have hrun_goal : ∃ o st' c,
      Runs w p ω (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) st o st' c ∧
      (o = .normal ∧ ∃ x',
        SameStaticConcrete x x' ∧
        (LSFRep x.h).rep b S' x' st'.mem ∧
        (∀ a_addr, a_addr < b ∨ x.endAddr b ≤ a_addr → st'.mem a_addr = st.mem a_addr) ∧
        StackMemAt st'.mem thStackBase rest ∧
        PopRegsOk b x' st'.regs ∧
        st'.regs 23 = rest.length ∧
        lsfPhi b x' st'.mem + 500 * auxLogCap n0 + 1400 + 1100 * mSmall ≤ lsfPhi b x st.mem) ∧
      c ≤ 120 * auxLogCap n0 + 600 * mSmall + 1460 := by
    dsimp only [addOrigRootPopStepStmt]
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
    refine addOrigRootPopCut_seq_le hw16 h24_ltw h_dgF_fAnc haux_ltw (Or.inr (by omega)) hdgF_ltw
      hvCap_ltw hnv htn hzIdx_lt (by omega) hcut_lt hETail_ltw hEHead_ltw hIntA_ltw hIntB_ltw
      hisr_z_ltw hf_rcnt_ltw hrL_cnt_ltw hb_rcnt_ltw hrcnt1_ltw
      hr0 hr2 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr16 hr21 hr36 hr37
      ha_read hb_read hRcnt_mem (by rw [hrOrig_bang])
      (hMinUp S) hpre_min (hDgDel S.RF.F) hpre_del ?_
    intro mem1 pos1 regs2 hdgF1_raw hfr1 hreg2_lo hr2_23 hr2_25 hr2_26 hr2_27 hr2_28 hr2_32 hr2_33
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
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        exact hnot_ab (connected_trans (connected_symm (Finset.mem_filter.mp hv1).2)
          (Finset.mem_filter.mp hv2).2)
      rw [← Finset.card_union_of_disjoint hdisj_ab, holdSz_card]
      congr 1; ext v
      simp only [Finset.mem_union, Finset.mem_filter]
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
        haux_ltw,
        hInv'.to_RF_spanning.1, hdgF2,
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
    rcases runs_call_of_meetsContract (r := 34) (hBFS S'.RF.F) hargs_bfs hvals_bfs hpre_bfs ω with
      ⟨st3, c_bfs, v_bfs, hrun_bfs, hpost_bfs, _, hreg3_other, hc_bfs⟩
    have hv_bfs0 : v_bfs = 0 := by
      rcases hpost_bfs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hv0, _⟩; exact hv0
    subst hv_bfs0
    obtain ⟨x', hsame, hrep3, hmem3_outside_end, hstk3, hphi_drop⟩ :=
      addOrigRootPopStep_post hend_ltw hrep_orig hzIdx_lt hz_not hold_eq rfl hold_act rfl rfl
        hconn_zrC hRorig' hz_not_R hR' hInv' hcut_mem hF'_eq rfl rfl haV hbV hnot_ab
        hpart_V hother_conn hother_disj hroots_sep hstk_rest hdgF1 hfr1 rfl hnewSum_eq hpost_bfs
    have hreg_kept : ∀ r, r ≤ 21 ∨ r = 36 ∨ r = 37 → st3.regs r = st.regs r :=
      fun r hr => (hreg3_other r (by clear * - hr; omega)).trans (hreg2_lo r hr)
    have hr23_3 : st3.regs 23 = rest.length :=
      (hreg3_other 23 (by decide)).trans hr2_23
    have hPopRegs3 : PopRegsOk b x' st3.regs := by
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
    refine ⟨.normal, st3, c_bfs, hrun_bfs,
      ⟨rfl, x', hsame, hrep3, hmem3_outside_end, hstk3, hPopRegs3, hr23_3, hphi_drop⟩, ?_⟩
    simp only [splitCompBFSContract, argsSize, Expr.size, List.getD_cons_zero, List.getD_cons_succ] at hc_bfs ⊢
    change c_bfs ≤ 12 + (600 * mSmall + 700) + 1 at hc_bfs
    have hsum_le : 0 + 60 + (120 * auxLogCap n0 + 660) + c_bfs ≤ 120 * auxLogCap n0 + 600 * mSmall + 1460 := by
      clear * - hc_bfs; omega
    exact hsum_le
  obtain ⟨o, st', c, hrun, ⟨rfl, x', hsame, hrep', hfr', hstk', hregs', hr23', hphi_d⟩, hc⟩ := hrun_goal
  have hlog1 : 1 ≤ auxLogCap n0 := by dsimp [auxLogCap]; omega
  refine ⟨st', c, x', hrun, hsame, hrep', hfr', hstk', hregs', hr23', ?_⟩
  have hcm : c + 40 ≤ 500 * auxLogCap n0 + 1400 + 1100 * mSmall := by
    have : 120 * auxLogCap n0 + 600 * mSmall + 1460 + 40 ≤
        500 * auxLogCap n0 + 1400 + 1100 * mSmall := by clear * - hlog1; omega
    exact Nat.le_trans (Nat.add_le_add_right hc 40) this
  calc c + 40 + lsfPhi b x' st'.mem
      = lsfPhi b x' st'.mem + (c + 40) := Nat.add_comm _ _
    _ ≤ lsfPhi b x' st'.mem + (500 * auxLogCap n0 + 1400 + 1100 * mSmall) := Nat.add_le_add_left hcm _
    _ = lsfPhi b x' st'.mem + 500 * auxLogCap n0 + 1400 + 1100 * mSmall := by ring
    _ ≤ lsfPhi b x st.mem := hphi_d

/-- Verification of the pop loop `.while (.reg 23) (addOrigRootPopStepStmt ...)`, by induction on
`stk : List ℕ`. Each iteration pays for itself and contributes `30` toward the climb loop. -/
private lemma addOrigRootPopLoop_runs {w b idxMinUp idxDgDel idxBFS : ℕ}
    {p : Program} {ω : ℕ → Bool} {x0 : LSFConcrete}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x0.endAddr b < 2 ^ w)
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x0.vList x0.tOrigList))
    (hDgDel : ∀ F, MeetsContract w p idxDgDel (dgDeleteEdgeContract w x0.vCap (fECap x0.eCap x0.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F)) :
    ∀ (stk : List ℕ) (S : LSFState) (x : LSFConcrete) (st : State),
      SameStaticConcrete x0 x →
      (LSFRep x0.h).rep b S x st.mem →
      PopRegsOk b x st.regs →
      st.regs 23 = stk.length →
      stk.length ≤ hldDepthBound x0.n0 →
      StackMemAt st.mem (auxThStackBase (lsfAuxPtr b x0.vCap x0.eCap x0.n0 x0.tM x0.L_w) x0.vCap x0.n0) stk →
      ThStackInv S x0.vList x0.thParent x0.n0 stk →
      ∃ st' c x',
        Runs w p ω (.loop (.reg 23) (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS)) st .normal st' c ∧
        SameStaticConcrete x0 x' ∧
        (LSFRep x0.h).rep b (applyThStack S x0.vList stk) x' st'.mem ∧
        (∀ a, a < b ∨ x0.endAddr b ≤ a → st'.mem a = st.mem a) ∧
        c + 30 * stk.length + lsfPhi b x' st'.mem ≤ 5 + lsfPhi b x st.mem := by
  intro stk
  induction stk with
  | nil =>
    intro S x st hsame hrep _ hr23 _ _ _
    have hcond : (Expr.reg 23).eval w st = some 0 := by
      have := Expr.eval_reg (w := w) 23 st; rwa [hr23] at this
    refine ⟨st, _, x, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hsame, hrep, fun _ _ => rfl, ?_⟩
    dsimp [Expr.size]; omega
  | cons zIdx rest ih =>
    intro S x st hsame hrep hregs hr23 hlen hstk hThInv
    have hcond : (Expr.reg 23).eval w st = some (rest.length + 1) := by
      have := Expr.eval_reg (w := w) 23 st; rwa [hr23] at this
    have hend_x : x.endAddr b < 2 ^ w := hsame.endAddr b ▸ hend_ltw
    have hx_h : x.h = x0.h := hsame.2.2.2.2.2.1
    have hx_vL : x.vList = x0.vList := hsame.2.2.2.2.2.2.2.2.2.2.2.1
    have hx_tL : x.tOrigList = x0.tOrigList := hsame.2.2.2.2.2.2.2.2.2.2.1
    have hx_vC : x.vCap = x0.vCap := hsame.1
    have hx_eC : x.eCap = x0.eCap := hsame.2.1
    have hx_n0 : x.n0 = x0.n0 := hsame.2.2.1
    have hx_tM : x.tM = x0.tM := hsame.2.2.2.2.1
    have hx_Lw : x.L_w = x0.L_w := hsame.2.2.2.2.2.2.2.2.1
    have hx_thp : x.thParent = x0.thParent := hsame.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hstk_x : StackMemAt st.mem (auxThStackBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0) (zIdx :: rest) := by
      rw [hx_vC, hx_eC, hx_n0, hx_tM, hx_Lw]; exact hstk
    have hThInv_x : ThStackInv S x.vList x.thParent x.n0 (zIdx :: rest) := by
      rw [hx_vL, hx_thp, hx_n0]; exact hThInv
    obtain ⟨st1, c1, x1, hrun1, hsame1, hrep1, hfr1, hstk1, hregs1, hr23_1, hc1⟩ :=
      addOrigRootPopStep_runs hw16 hend_x (hx_h.symm ▸ hrep)
        (by rw [hx_vL, hx_tL]; exact hMinUp) (by rw [hx_vC, hx_eC, hx_n0]; exact hDgDel)
        hBFS hregs hr23 (by rw [hx_n0]; exact hlen) hstk_x hThInv_x
    have hsame01 : SameStaticConcrete x0 x1 := hsame.trans hsame1
    have hstk1' : StackMemAt st1.mem (auxThStackBase (lsfAuxPtr b x0.vCap x0.eCap x0.n0 x0.tM x0.L_w) x0.vCap x0.n0) rest := by
      rwa [hx_vC, hx_eC, hx_n0, hx_tM, hx_Lw] at hstk1
    have hThInv_rest : ThStackInv { S with R₀_base := insert (x0.vList[zIdx]!) S.R₀_base }
        x0.vList x0.thParent x0.n0 rest := hThInv.2.2.2.2
    obtain ⟨st2, c2, x2, hrun2, hsame02, hrep2, hfr2, hc2⟩ :=
      ih { S with R₀_base := insert (x0.vList[zIdx]!) S.R₀_base } x1 st1 hsame01
        (hx_h ▸ hx_vL ▸ hrep1) hregs1 hr23_1 (by simp at hlen; omega) hstk1' hThInv_rest
    refine ⟨st2, _, x2, runs_loop_iff.mpr (Or.inr (Or.inr ⟨rest.length + 1, st1, c1, c2, hcond, Nat.succ_ne_zero _, hrun1, hrun2, rfl⟩)),
      hsame02, hrep2, fun a ha => (hfr2 a ha).trans (hfr1 a (by rw [hsame.endAddr b]; exact ha)), ?_⟩
    simp only [List.length_cons, Expr.size]
    omega

/-! ## Top-level `addOrigRootProc` verification -/

/-- Full amortized verification of `addOrigRootProc`: inserts `u ∈ S.T₀.V` into `S.R₀_base`,
maintaining `LSFRep h`, preserving memory outside `[b, x.endAddr b)`, and paying at most
`250` amortized cost (`c + lsfPhi b x' mem' ≤ 250 + lsfPhi b x mem`). -/
theorem addOrigRoot_runs {w h b u idxMinUp idxDgDel idxBFS : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete}
    {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep h).rep b S x mem)
    (huT : u ∈ S.T₀.V)
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDel : ∀ F, MeetsContract w p idxDgDel (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F)) :
    let S' : LSFState := { S with R₀_base := insert u S.R₀_base }
    ∃ st' c x',
      Runs w p ω (addOrigRootProc idxMinUp idxDgDel idxBFS)
        (startState [b, u] mem pos) (.returned 0) st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep b S' x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
      c + lsfPhi b x' st'.mem ≤ 250 + lsfPhi b x mem := by
  intro S'
  have hxH : x.h = h := hrep.1
  subst hxH
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set isRootBase := fIsRootBase fAncPtr
  have hlay := addRoot_layout hend_ltw
  have hrep_copy := hrep
  rcases hrep with ⟨_, _, _, _, _, _, hInv, hn0, _, _, _, _, _, _, hvT_lt, _,
    _, _, _, _, hFAnc, _, _, hAux⟩
  rcases hFAnc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hIsR_mem, _⟩
  rcases hAux with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvLen, _, hvMem, _⟩
  have hu_vCap : u < vCap := hvT_lt u huT
  have hisr_u_ltw : isRootBase + u < 2 ^ w := by
    dsimp [isRootBase, fAncPtr, vCap, eCap, n0, tM, fIsRootBase, fAncSize] at hlay ⊢; omega
  have hu_in_R_iff : u ∈ S.RF.R ↔ u ∈ S.R_orig := by
    simp only [LSFState.RF, LSFState.R, Finset.mem_union]
    exact ⟨fun h => h.resolve_right (Finset.disjoint_left.mp hInv.hdisj_iso huT), Or.inl⟩
  have hInv' : LSFStructInv S' := (hInv.addOrigRoot_inv huT).1
  have hTH := hldAuxTree_isRootedTree hInv.hT₀
  -- Step 1: run header loads (`addOrigRootHdr_triple`)
  obtain ⟨o0, st0, c0, hrun0, hq0, hc0⟩ :=
    addOrigRootHdr_triple (w := w) (b := b) (u := u) (p := p) hw16 hend_ltw hrep_copy
      (startState [b, u] mem pos) ω ⟨rfl, rfl, rfl⟩
  cases o0 with
  | returned _ => exact False.elim hq0
  | normal =>
    rcases hq0 with ⟨hmem0, hr0_0, hr0_1, hr0_2, hr0_3, hr0_4, hr0_5, hr0_6, hr0_7, hr0_8, hr0_9, hr0_10⟩
    by_cases hu_R : u ∈ S.R_orig
    · -- Fast path: `fIsRoot[u] = 1`, return 0 immediately
      have hcond_eval : (Expr.load (.bin .add (.reg 10) (.reg 1))).eval w st0 = some 1 :=
        Expr.eval_load_of_eq (by eval_expr) (by rw [hmem0, hIsR_mem u hu_vCap, ite_eq_left (hu_in_R_iff.mpr hu_R)])
      have hret_run : Runs w p ω (.ret (.const 0)) st0 (.returned 0) st0 ((Expr.const 0).size + 1) :=
        runs_ret_iff.mpr ⟨0, Expr.eval_const (k := 0) (by omega), rfl, rfl, rfl⟩
      have hcond_run : Runs w p ω
          (.cond (.load (.bin .add (.reg 10) (.reg 1))) (.ret (.const 0))
            (addOrigRootSetupStmt ;; addOrigRootClimbStmt ;;
             .loop (.reg 23) (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0)))
          st0 (.returned 0) st0 ((Expr.load (.bin .add (.reg 10) (.reg 1))).size + ((Expr.const 0).size + 1) + 1) :=
        runs_cond_iff.mpr ⟨1, _, hcond_eval, by simpa using hret_run, rfl⟩
      have hfull : Runs w p ω (addOrigRootProc idxMinUp idxDgDel idxBFS)
          (startState [b, u] mem pos) (.returned 0) st0 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st0, c0, _, hrun0, hcond_run, rfl⟩)
      have hRorig_eq : S'.R_orig = S.R_orig := by
        ext w; change w ∈ upClosure S.TH S.r₀ (insert u S.R₀_base) ↔ w ∈ S.R_orig
        rw [mem_upClosure_iff]
        constructor
        · rintro ⟨v, hv, hwv⟩
          rw [Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact upClosure_isUpwardClosed hTH hInv.hR₀_sub hu_R hwv
          · exact mem_upClosure_iff.mpr ⟨v, hv, hwv⟩
        · intro hw
          obtain ⟨v, hv, hwv⟩ := mem_upClosure_iff.mp hw
          exact ⟨v, Finset.mem_insert_of_mem hv, hwv⟩
      have hrep' : (LSFRep x.h).rep b S' x st0.mem :=
        lsfRep_of_R_orig_eq (S₁ := S) (S₂ := S') (hmem0.symm ▸ hrep_copy) hInv'
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hRorig_eq
      refine ⟨st0, _, x, hfull, SameStaticConcrete.refl x, hrep', fun _ _ => by rw [hmem0], ?_⟩
      rw [hmem0]; dsimp [Expr.size] at *; omega
    · -- Slow path: `fIsRoot[u] = 0`, run setup + climb + pop loop + ret 0
      have hcond_eval : (Expr.load (.bin .add (.reg 10) (.reg 1))).eval w st0 = some 0 :=
        Expr.eval_load_of_eq (by eval_expr) (by
          rw [hmem0, hIsR_mem u hu_vCap, ite_eq_right (fun h => hu_R (hu_in_R_iff.mp h))])
      obtain ⟨uIdx, huIdx_lt, hu_get⟩ := List.mem_iff_getElem.mp ((hvMem u).mpr huT)
      have hu_bang : x.vList[uIdx]! = u := by rw [getElem!_pos x.vList uIdx huIdx_lt]; exact hu_get
      -- Step 2: setup
      obtain ⟨o1, st1, c1, hrun1, hq1, hc1⟩ :=
        addOrigRootSetup_triple (w := w) (b := b) (u := u) (p := p) (regs_in := st0.regs)
          hw16 hend_ltw hrep_copy (by omega) hu_bang st0 ω
          ⟨hmem0, rfl, hr0_1, hr0_2, hr0_3, hr0_4, hr0_7, hr0_8, hr0_9⟩
      cases o1 with
      | returned _ => exact False.elim hq1
      | normal =>
        rcases hq1 with ⟨hmem1, hr1_11, hr1_12, hr1_13, hr1_14, hr1_15, hr1_16, hr1_17, hr1_18,
          hr1_19, hr1_20, hr1_21, hr1_36, hr1_37, hr1_22, hr1_23, hr1_lo⟩
        -- Step 3: climb
        have hdu_le : (S.TH.forestPath (x.vList[uIdx]!) S.r₀).length ≤ hldDepthBound n0 := by
          rw [hu_bang]
          have hh := hldAuxTree_height hInv.hT₀ huT
          dsimp [depth] at hh
          rw [hInv.hTV] at hh
          have hcard : S.G₀.V.card = n0 := hn0
          rw [hcard] at hh
          exact hh
        obtain ⟨st2, c2, stk, hrun2, hfr2, hstk2, _, _, hlen_bd, hThInv, hanc_sub, hanc_cov,
          hr2_23, hreg2, hc2⟩ :=
          addOrigRootClimb_runs hw16 hend_ltw hrep_copy
            (S.TH.forestPath (x.vList[uIdx]!) S.r₀).length uIdx [] st1
            (by omega) rfl (by simp only [List.length_nil, Nat.zero_add]; exact hdu_le)
            (fun a _ => hmem1 ▸ rfl) (fun _ hi => by simp at hi) List.nodup_nil
            (fun _ hi => by simp at hi) (fun _ hi => by simp at hi) (fun _ _ h => by cases h)
            ((hr1_lo 10 (by decide)).trans hr0_10) hr1_12 hr1_13 hr1_14 hr1_22 hr1_23
        obtain ⟨hrep2, hphi2⟩ := lsfRep_of_thStack_write hrep_copy hfr2
        have hPopRegs2 : PopRegsOk b x st2.regs :=
          ⟨(hreg2 0 (by decide) (by decide)).trans ((hr1_lo 0 (by decide)).trans hr0_0),
            (hreg2 2 (by decide) (by decide)).trans ((hr1_lo 2 (by decide)).trans hr0_2),
            (hreg2 4 (by decide) (by decide)).trans ((hr1_lo 4 (by decide)).trans hr0_4),
            (hreg2 5 (by decide) (by decide)).trans ((hr1_lo 5 (by decide)).trans hr0_5),
            (hreg2 6 (by decide) (by decide)).trans ((hr1_lo 6 (by decide)).trans hr0_6),
            (hreg2 7 (by decide) (by decide)).trans ((hr1_lo 7 (by decide)).trans hr0_7),
            (hreg2 8 (by decide) (by decide)).trans ((hr1_lo 8 (by decide)).trans hr0_8),
            (hreg2 9 (by decide) (by decide)).trans ((hr1_lo 9 (by decide)).trans hr0_9),
            (hreg2 10 (by decide) (by decide)).trans ((hr1_lo 10 (by decide)).trans hr0_10),
            (hreg2 11 (by decide) (by decide)).trans hr1_11,
            (hreg2 12 (by decide) (by decide)).trans hr1_12,
            (hreg2 14 (by decide) (by decide)).trans hr1_14,
            (hreg2 15 (by decide) (by decide)).trans hr1_15,
            (hreg2 16 (by decide) (by decide)).trans hr1_16,
            (hreg2 17 (by decide) (by decide)).trans hr1_17,
            (hreg2 18 (by decide) (by decide)).trans hr1_18,
            (hreg2 19 (by decide) (by decide)).trans hr1_19,
            (hreg2 20 (by decide) (by decide)).trans hr1_20,
            (hreg2 21 (by decide) (by decide)).trans hr1_21,
            (hreg2 36 (by decide) (by decide)).trans hr1_36,
            (hreg2 37 (by decide) (by decide)).trans hr1_37⟩
        -- Step 4: pop loop
        obtain ⟨st3, c3, x', hrun3, hsame', hrep3, hfr3, hc3⟩ :=
          addOrigRootPopLoop_runs hw16 hend_ltw hMinUp hDgDel hBFS stk S x st2
            (SameStaticConcrete.refl x) hrep2 hPopRegs2 hr2_23 hlen_bd hstk2 hThInv
        -- Step 5: return 0
        have hret_run : Runs w p ω (.ret (.const 0)) st3 (.returned 0) st3 ((Expr.const 0).size + 1) :=
          runs_ret_iff.mpr ⟨0, Expr.eval_const (k := 0) (by omega), rfl, rfl, rfl⟩
        have hseq3 : Runs w p ω
            (.loop (.reg 23) (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0))
            st2 (.returned 0) st3 (c3 + ((Expr.const 0).size + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, hrun3, hret_run, rfl⟩)
        have hseq2 : Runs w p ω
            (addOrigRootClimbStmt ;;
             .loop (.reg 23) (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0))
            st1 (.returned 0) st3 (c2 + (c3 + ((Expr.const 0).size + 1) + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2, hseq3, rfl⟩)
        have hseq1 : Runs w p ω
            (addOrigRootSetupStmt ;; addOrigRootClimbStmt ;;
             .loop (.reg 23) (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0))
            st0 (.returned 0) st3 (c1 + (c2 + (c3 + ((Expr.const 0).size + 1) + 1) + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hrun1, hseq2, rfl⟩)
        have hcond_run : Runs w p ω
            (.cond (.load (.bin .add (.reg 10) (.reg 1))) (.ret (.const 0))
              (addOrigRootSetupStmt ;; addOrigRootClimbStmt ;;
               .loop (.reg 23) (addOrigRootPopStepStmt idxMinUp idxDgDel idxBFS) ;; .ret (.const 0)))
            st0 (.returned 0) st3 _ :=
          runs_cond_iff.mpr ⟨0, _, hcond_eval, by simpa using hseq1, rfl⟩
        have hfull : Runs w p ω (addOrigRootProc idxMinUp idxDgDel idxBFS)
            (startState [b, u] mem pos) (.returned 0) st3 _ :=
          runs_seq_iff.mpr (Or.inr ⟨st0, c0, _, hrun0, hcond_run, rfl⟩)
        -- Show `(applyThStack S x.vList stk).R_orig = S'.R_orig`
        have hflds := applyThStack_fields S x.vList stk
        have hRorig_eq : S'.R_orig = (applyThStack S x.vList stk).R_orig := by
          ext w
          have hTH_eq : (applyThStack S x.vList stk).TH = S.TH := by
            simp only [LSFState.TH, hflds.2.2.1, hflds.2.2.2.1]
          change w ∈ upClosure S.TH S.r₀ (insert u S.R₀_base) ↔
            w ∈ upClosure (applyThStack S x.vList stk).TH (applyThStack S x.vList stk).r₀
              (applyThStack S x.vList stk).R₀_base
          rw [hTH_eq, hflds.2.2.2.1, hflds.2.2.2.2.2.2.2.2.2.2.2.2.2,
            mem_upClosure_iff, mem_upClosure_iff]
          constructor
          · rintro ⟨v, hv, hwv⟩
            rw [Finset.mem_insert] at hv
            rcases hv with rfl | hv
            · rw [← hu_bang] at hwv
              rcases hanc_cov w hwv with hwR | ⟨idx, hidx, rfl⟩
              · obtain ⟨v0, hv0, hwv0⟩ := mem_upClosure_iff.mp hwR
                exact ⟨v0, Finset.mem_union_left _ hv0, hwv0⟩
              · exact ⟨x.vList[idx]!, Finset.mem_union_right _
                  (List.mem_toFinset.mpr (List.mem_map.mpr ⟨idx, hidx, rfl⟩)),
                  isAncestor_refl _ _ _⟩
            · exact ⟨v, Finset.mem_union_left _ hv, hwv⟩
          · rintro ⟨v, hv, hwv⟩
            rw [Finset.mem_union] at hv
            rcases hv with hv | hv
            · exact ⟨v, Finset.mem_insert_of_mem hv, hwv⟩
            · obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
              have hv_anc : IsAncestor S.TH S.r₀ (x.vList[idx]!) u := by
                rcases hanc_sub _ ⟨idx, hidx, rfl⟩ with h1 | ⟨_, h2, _⟩
                · rwa [hu_bang] at h1
                · simp at h2
              exact ⟨u, Finset.mem_insert_self _ _, isAncestor_trans hTH huT hwv hv_anc⟩
        have hrep_final : (LSFRep x.h).rep b S' x' st3.mem :=
          lsfRep_of_R_orig_eq hrep3 hInv'
            hflds.1.symm hflds.2.1.symm hflds.2.2.1.symm hflds.2.2.2.1.symm hflds.2.2.2.2.1.symm
            hflds.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.2.1.symm
            hflds.2.2.2.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.2.2.2.1.symm
            hflds.2.2.2.2.2.2.2.2.2.2.1.symm hflds.2.2.2.2.2.2.2.2.2.2.2.1.symm
            hflds.2.2.2.2.2.2.2.2.2.2.2.2.1.symm hRorig_eq
        have hfr_final : ∀ a_addr, a_addr < b ∨ x.endAddr b ≤ a_addr → st3.mem a_addr = mem a_addr := by
          intro a_addr ha
          rw [hfr3 a_addr ha]
          exact hfr2 a_addr (fun hc => by
            dsimp [auxThStackBase, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
              auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
              auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase] at hlay hc
            omega)
        refine ⟨st3, _, x', hfull, hsame', hrep_final, hfr_final, ?_⟩
        dsimp only [Expr.size] at hc0 hc1 hc2 hc3 ⊢
        simp only [List.length_nil, Nat.sub_zero] at hc2
        rw [hphi2] at hc3
        omega

/-- Call-wrapper for `addOrigRoot_runs`, directly usable by `BatchOps` when invoking
`.call r idxAddRoot args` on `[b, u]`. -/
theorem addOrigRoot_call_runs {w h b u r idxAddRoot idxMinUp idxDgDel idxBFS : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete}
    {args : List Expr} {st : State}
    (hp : p.procs[idxAddRoot]? = some (addOrigRootProc idxMinUp idxDgDel idxBFS))
    (hargs : evalArgs w st args = some [b, u])
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w)
    (hrep : (LSFRep h).rep b S x st.mem)
    (huT : u ∈ S.T₀.V)
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDel : ∀ F, MeetsContract w p idxDgDel (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F)) :
    let S' : LSFState := { S with R₀_base := insert u S.R₀_base }
    ∃ st' c x',
      Runs w p ω (.call r idxAddRoot args) st .normal st' c ∧
      st'.regs = Function.update st.regs r 0 ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep b S' x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = st.mem a) ∧
      c + lsfPhi b x' st'.mem ≤ argsSize args + 255 + lsfPhi b x st.mem := by
  intro S'
  obtain ⟨st1, c1, x', hrun1, hsame, hrep', hfr, hcost⟩ :=
    addOrigRoot_runs (pos := st.pos) hw16 hend_ltw hrep huT hMinUp hDgDel hBFS
  refine ⟨{ st1 with regs := Function.update st.regs r 0 }, argsSize args + c1 + 1, x',
    runs_call_iff.mpr ⟨[b, u], addOrigRootProc idxMinUp idxDgDel idxBFS,
      .returned 0, st1, c1, hargs, hp, hrun1, rfl, rfl, rfl⟩,
    rfl, hsame, hrep', hfr, by dsimp only; omega⟩

end

end MinCostFlow.LSF.Program
