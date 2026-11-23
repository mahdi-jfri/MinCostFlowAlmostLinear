module

public import MinCostFlow.LSF.Program.BatchSplitOpTail
import Mathlib.Tactic.Linarith

/-!
# Vertex-Split Procedure for Dynamic LSF (`BatchSplitOp`)

Verifies `lsfSplitUpdate_runs` (`Lemma 5.4`, `arXiv:2309.16629v1` page 17 and Appendix A.1 page 48),
combining the prefix register setup (`lsfSplitUpdate_prefix`), `T_H`-closure (`addOrigRoot_call_runs`),
and the post-closure tail (`lsfSplitUpdate_tail`) with amortized bound `3000 * len`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 1200000 in
theorem lsfSplitUpdate_runs
    {w h b updPtr v v' len idxAddRoot idxMinUp idxDgDelF idxDgUpd idxBFS idxTSplit : ℕ}
    {St Sh : Finset ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x : LSFConcrete} {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w) (hupd_ltw : updPtr + len < 2 ^ w)
    (hdisj_upd : ∀ i < len, updPtr + i < b ∨ x.endAddr b ≤ updPtr + i)
    (hupd_word : ∀ i < len, mem (updPtr + i) < 2 ^ w)
    (hrep : (LSFRep h).rep b S x mem)
    (hu_valid : S.G.UpdateIsValid (.split v v' St Sh))
    (hv'_cap : v' < x.vCap)
    (hcan_t : ∀ e ∈ St, e ∈ S.G.E ∧ S.G.tail e = v)
    (hcan_h : ∀ e ∈ Sh, e ∈ S.G.E ∧ S.G.head e = v)
    (hUpdAt : UpdateAt mem updPtr S.G (.split v v' St Sh) len)
    (hpAdd : p.procs[idxAddRoot]? = some (addOrigRootProc idxMinUp idxDgDelF idxBFS))
    (hMinUp : ∀ S₀, MeetsContract w p idxMinUp (minEdgeUpContract w S₀ x.vList x.tOrigList))
    (hDgDelF : ∀ F, MeetsContract w p idxDgDelF (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) F))
    (hDgUpdF : ∀ G H, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x.vCap (fECap x.eCap x.n0) G H (.split v v' St Sh) len))
    (hDgUpdG : ∀ G, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x.vCap x.eCap G G (.split v v' St Sh) len))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F))
    (hTSplit : ∀ G T_cur, MeetsContract w p idxTSplit
      (lsfTBlockSplitContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList v v' St Sh len)) :
    ∃ st' c x',
      Runs w p ω (lsfSplitUpdateProc idxAddRoot idxDgUpd idxBFS idxTSplit)
        (startState [b, updPtr] mem pos) (.returned len) st' c ∧
      SameStaticConcrete x x' ∧
      (LSFRep h).rep b (applyLSFUpdate S (.split v v' St Sh)) x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem a) ∧
      c + lsfPhi b x' st'.mem ≤ 3000 * len + lsfPhi b x mem := by
  classical
  set vCap := x.vCap; set eCap := x.eCap; set n0 := x.n0; set tM := x.tM; set L_w := x.L_w
  set eCapF := fECap eCap n0
  set dgGPtr := lsfDgGPtr b
  set tPtr := lsfTBlockPtr b vCap eCap
  set dgFPtr := lsfDgFPtr b vCap eCap tM
  set fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  set wPtr := lsfWBlockPtr b vCap eCap n0 tM
  set auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  set wstrNumPtr := lsfWstrNumPtr b vCap eCap n0 tM
  set wstrDenPtr := lsfWstrDenPtr b vCap eCap n0 tM L_w
  set origBase := auxOrigVertBase auxPtr vCap n0
  set isOrigBase := auxIsOrigVertBase auxPtr vCap n0
  rcases lsfBlock_disjoint' b vCap eCap n0 tM L_w with ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9⟩
  change b + lsfHdrSize = dgGPtr at hl1
  have hb_lt_fAnc : b + 24 ≤ fAncPtr := by dsimp [lsfHdrSize] at hl1; omega
  change dgGPtr + dynGraphSize vCap eCap = tPtr at hl2
  change tPtr + tBlockSize vCap eCap tM = dgFPtr at hl3
  have hb_lt_dgF : b + 24 ≤ dgFPtr := by dsimp [lsfHdrSize] at hl1; omega
  change dgFPtr + dynGraphSize vCap eCapF = fAncPtr at hl4
  change fAncPtr + fAncSize vCap = wPtr at hl5
  change wPtr + wBlockSize n0 = auxPtr at hl6
  change auxPtr + auxSize vCap n0 = wstrNumPtr at hl7
  change wstrNumPtr + eCap * L_w = wstrDenPtr at hl8
  change wstrDenPtr + eCap * L_w = lsfEndAddr b vCap eCap n0 tM L_w at hl9
  have hfAnc_bds :
      fAncPtr + fOffRCount < fIsRootBase fAncPtr ∧
      fIsRootBase fAncPtr + vCap = fRListBase fAncPtr vCap ∧
      fRListBase fAncPtr vCap + vCap = fCompIdBase fAncPtr vCap ∧
      fCompIdBase fAncPtr vCap + vCap = fCompRootBase fAncPtr vCap ∧
      fCompRootBase fAncPtr vCap + vCap = fCompSizeBase fAncPtr vCap ∧
      fCompSizeBase fAncPtr vCap + vCap = fAncPtr + fAncSize vCap := by
    dsimp only [fIsRootBase, fRListBase, fCompIdBase, fCompRootBase, fCompSizeBase,
      fOffRCount, fAncHdrSize, fAncSize]; omega
  have haux_bds :
      auxPtr + auxHdrSize ≤ origBase ∧
      origBase + vCap = isOrigBase ∧
      isOrigBase + vCap = auxQBufABase auxPtr vCap n0 ∧
      auxQBufABase auxPtr vCap n0 + vCap = auxQBufBBase auxPtr vCap n0 ∧
      auxQBufBBase auxPtr vCap n0 + vCap = auxVisABase auxPtr vCap n0 ∧
      auxVisABase auxPtr vCap n0 + vCap = auxVisBBase auxPtr vCap n0 ∧
      auxVisBBase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
    dsimp only [origBase, isOrigBase, auxOrigVertBase, auxIsOrigVertBase, auxQBufABase,
      auxQBufBBase, auxVisABase, auxVisBBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
      auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase,
      auxHdrSize, auxSize]; omega
  have hend_eq : x.endAddr b = lsfEndAddr b vCap eCap n0 tM L_w := rfl
  have hrep_orig := hrep
  rcases hrep with ⟨hxH, hh1, hLin, hLw, hkn, hkeq, hInv, hn0, hm0, htM, hnv, hme, htn, hn1,
    hvT_lt, heG_lt, hhdr, hdgG, hT, hdgF, hFAnc, hW, hwstr, hAux⟩
  -- Unpack split encoding at `updPtr`
  have hUpd_cases : ∃ tag Lt Lh,
      (tag = 2 ∨ tag = 3) ∧ len = 5 + Lt.length + Lh.length ∧
      ListAt mem updPtr ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
    rcases hUpdAt with ⟨Lt, Lh, _, _, _, _, hlen, hLA⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hLA⟩
    · exact ⟨2, Lt, Lh, Or.inl rfl, hlen, hLA⟩
    · exact ⟨3, Lt, Lh, Or.inr rfl, hlen, hLA⟩
  rcases hUpd_cases with ⟨tag, Lt, Lh, htag_23, hlen_eq, hLA_upd⟩
  set kt := Lt.length; set kh := Lh.length
  have hmem_u : ∀ i (hi : i < 5), mem (updPtr + i) = ([tag, v, v', kt, kh] : List ℕ)[i]'(by simp; omega) := by
    intro i hi
    have hi' : i < ([tag, v, v', kt, kh] ++ Lt ++ Lh).length := by simp [kt, kh]; omega
    have h := hLA_upd i hi'
    simp only [List.append_assoc] at hi' h
    rw [List.getElem_append_left (by simp; omega)] at h
    exact h
  have htag_m : mem updPtr = tag := by simpa using hmem_u 0 (by decide)
  have hv_m : mem (updPtr + 1) = v := hmem_u 1 (by decide)
  have hv'_m : mem (updPtr + 2) = v' := hmem_u 2 (by decide)
  have hkt_m : mem (updPtr + 3) = kt := hmem_u 3 (by decide)
  have hkh_m : mem (updPtr + 4) = kh := hmem_u 4 (by decide)
  -- Bounds
  have hstep := applyLSFUpdate_split_step hInv hu_valid
  set vOrig := S.origVert v
  set S₁ : LSFState := { S with R₀_base := insert vOrig S.R₀_base }
  set S' : LSFState := applyLSFUpdate S (.split v v' St Sh)
  have hvOrig_T : vOrig ∈ S.T₀.V := hstep.1
  have hInv₁ : LSFStructInv S₁ := hstep.2.1
  have hInv' : LSFStructInv S' := hstep.2.2.1
  have hRorig' : S'.R_orig = S₁.R_orig := hstep.2.2.2.1
  have hv_R1 : v ∈ S₁.R := hstep.2.2.2.2.1
  have hv'_not_R1 : v' ∉ S₁.R := hstep.2.2.2.2.2.1
  have hR' : S'.R = insert v' S₁.R := hstep.2.2.2.2.2.2.1
  have hFres_congr := hstep.2.2.2.2.2.2.2.1
  have hvG : v ∈ S.G.V := hu_valid.1
  have hv_lt : v < vCap := hdgG.2.1 v hvG
  have hvOrig_lt : vOrig < vCap := hvT_lt vOrig hvOrig_T
  have hb_hdr_ltw : b + lsfHdrSize < 2 ^ w := by omega
  have hdgG_end_ltw : dgGPtr + dynGraphSize vCap eCap < 2 ^ w := by omega
  have htPtr_end_ltw : tPtr + tBlockSize vCap eCap tM < 2 ^ w := by omega
  have hdgF_end_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w := by omega
  have hfAnc_end_ltw : fAncPtr + fAncSize vCap < 2 ^ w := by omega
  have haux_end_ltw : auxPtr + auxSize vCap n0 < 2 ^ w := by omega
  have hvCap_ltw : vCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have heCap_ltw : eCap < 2 ^ w := by dsimp [dynGraphSize] at hdgG_end_ltw; omega
  have heCapF_ltw : eCapF < 2 ^ w := by dsimp [dynGraphSize] at hdgF_end_ltw; omega
  have h3eCap_ltw : 3 * eCap < 2 ^ w := by dsimp [eCapF, fECap] at heCapF_ltw; omega
  have hn0_ltw : n0 < 2 ^ w := by omega
  have htM_ltw : tM < 2 ^ w := by omega
  have hv_ltw : v < 2 ^ w := by omega
  have hv'_ltw : v' < 2 ^ w := by omega
  have hvOrig_ltw : vOrig < 2 ^ w := by omega
  have hkt_ltw : kt < 2 ^ w := by omega
  have hkh_ltw : kh < 2 ^ w := by omega
  have hlen_ltw : len < 2 ^ w := by omega
  have horig_end_ltw : origBase + vCap < 2 ^ w := by
    dsimp [origBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
      auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize] at haux_end_ltw ⊢
    omega
  have hisOrig_end_ltw : isOrigBase + vCap < 2 ^ w := by
    dsimp [isOrigBase, auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
      auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase,
      auxVIdxBase, auxSize] at haux_end_ltw ⊢
    omega
  have horig_ptr_m : mem (auxPtr + auxOffOrigVertPtr) = origBase := hAux.2.2.2.2.2.2.2.2.2.1
  have hisOrig_ptr_m : mem (auxPtr + auxOffIsOrigVertPtr) = isOrigBase := hAux.2.2.2.2.2.2.2.2.2.2.1
  have hvOrig_m : mem (origBase + v) = vOrig :=
    hAux.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v hvG hv_lt
  have hb24 : b + 24 < 2 ^ w := hb_hdr_ltw
  have haux20 : auxPtr + 20 < 2 ^ w := by dsimp [auxSize, auxHdrSize] at haux_end_ltw; omega
  have hr0 : (startState [b, updPtr] mem pos).regs 0 = b := by simp [startState]
  have hr1 : (startState [b, updPtr] mem pos).regs 1 = updPtr := by simp [startState]
  -- Phase 1: direct state `st0` after the 16 prefix assigns
  let st0 : State :=
    { mem := mem
      regs := Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (startState [b, updPtr] mem pos).regs
          2 vCap) 3 eCap) 4 n0) 5 tM) 6 dgGPtr) 7 tPtr) 8 dgFPtr) 9 fAncPtr) 10 auxPtr)
          11 v) 12 v') 13 kt) 14 kh) 15 origBase) 16 isOrigBase) 17 vOrig
      pos := pos }
  have hmem0 : st0.mem = mem := rfl
  have hr0_0 : st0.regs 0 = b := by dsimp [st0]; simp [hr0]
  have hr0_1 : st0.regs 1 = updPtr := by dsimp [st0]; simp [hr1]
  have hr0_2 : st0.regs 2 = vCap := by dsimp [st0]; simp
  have hr0_3 : st0.regs 3 = eCap := by dsimp [st0]; simp
  have hr0_4 : st0.regs 4 = n0 := by dsimp [st0]; simp
  have hr0_5 : st0.regs 5 = tM := by dsimp [st0]; simp
  have hr0_6 : st0.regs 6 = dgGPtr := by dsimp [st0]; simp
  have hr0_7 : st0.regs 7 = tPtr := by dsimp [st0]; simp
  have hr0_8 : st0.regs 8 = dgFPtr := by dsimp [st0]; simp
  have hr0_9 : st0.regs 9 = fAncPtr := by dsimp [st0]; simp
  have hr0_10 : st0.regs 10 = auxPtr := by dsimp [st0]; simp
  have hr0_11 : st0.regs 11 = v := by dsimp [st0]; simp
  have hr0_12 : st0.regs 12 = v' := by dsimp [st0]; simp
  have hr0_13 : st0.regs 13 = kt := by dsimp [st0]; simp
  have hr0_14 : st0.regs 14 = kh := by dsimp [st0]; simp
  have hr0_15 : st0.regs 15 = origBase := by dsimp [st0]; simp
  have hr0_16 : st0.regs 16 = isOrigBase := by dsimp [st0]; simp
  have hr0_17 : st0.regs 17 = vOrig := by dsimp [st0]; simp
  -- Phase 2: Call addOrigRoot(b, vOrig)
  obtain ⟨st1, c1, x1, hrun1, hregs1, hsame1, hrep1, hfr1, hc1⟩ :=
    addOrigRoot_call_runs (ω := ω) (r := 18) (args := [.reg 0, .reg 17]) (st := st0)
      hpAdd (by eval_expr) hw16 hend_ltw (hmem0.symm ▸ hrep_orig) hvOrig_T hMinUp hDgDelF hBFS
  have hx1_vc : x1.vCap = vCap := hsame1.1
  have hx1_ec : x1.eCap = eCap := hsame1.2.1
  have hx1_n0 : x1.n0 = n0 := hsame1.2.2.1
  have hx1_tM : x1.tM = tM := hsame1.2.2.2.2.1
  have hx1_Lw : x1.L_w = L_w := hsame1.2.2.2.2.2.2.2.2.1
  have hx1_tL : x1.tOrigList = x.tOrigList := hsame1.2.2.2.2.2.2.2.2.2.2.1
  have hrep1_copy := hrep1
  rcases hrep1 with ⟨hxH1, hh1_1, hLin1, hLw1, hkn1, hkeq1, _, hn0_1, hm0_1, htM1, hnv1, hme1, htn1,
    hn1_1, hvT_lt1, heG_lt1, hhdr1, hdgG1, hT1, hdgF1, hFAnc1, hW1, hwstr1, hAux1⟩
  set mem1 := st1.mem
  have hupd_ag1 : ∀ i < len, mem1 (updPtr + i) = mem (updPtr + i) := fun i hi =>
    (hfr1 _ (hdisj_upd i hi)).trans (hmem0 ▸ rfl)
  have hUpdAt1 : UpdateAt mem1 updPtr S₁.G (.split v v' St Sh) len :=
    UpdateAt.of_agree hUpdAt hupd_ag1
  have hupd_word1 : ∀ i < len, mem1 (updPtr + i) < 2 ^ w := fun i hi => by
    rw [hupd_ag1 i hi]; exact hupd_word i hi
  -- Values loaded from `fAncPtr` in `mem1`
  obtain ⟨rCnt, hrCnt_def⟩ : ∃ rCnt : ℕ, rCnt = S₁.R.card := ⟨_, rfl⟩
  obtain ⟨oldCid, holdCid_def⟩ : ∃ oldCid : ℕ, oldCid = x1.compId v := ⟨_, rfl⟩
  obtain ⟨oldSize, holdSize_def⟩ : ∃ oldSize : ℕ, oldSize = x1.compSize oldCid := ⟨_, rfl⟩
  have hv_F1 : v ∈ S₁.RF.F.V := hInv₁.RF_V_eq ▸ hu_valid.1
  have hv'_not_F1 : v' ∉ S₁.RF.F.V := hInv₁.RF_V_eq ▸ hu_valid.2.1
  have hFAnc1' : FAncAt mem1 fAncPtr vCap S₁.RF x1.rList x1.compId x1.compRoot x1.compSize x1.activeCids := by
    simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM] using hFAnc1
  have hdgF1' : DynGraphAt mem1 dgFPtr vCap eCapF S₁.RF.F := by
    simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, eCapF] using hdgF1
  have hdgG1' : DynGraphAt mem1 dgGPtr vCap eCap S₁.G := by
    simpa only [hx1_vc, hx1_ec] using hdgG1
  have hT1' : TBlockAt mem1 tPtr vCap eCap tM S₁.G S₁.T_cur S.T₀ S.π x.tOrigList := by
    simpa only [hx1_vc, hx1_ec, hx1_tM, hx1_tL, tPtr] using hT1
  have hcid_m1 : mem1 (fCompIdBase fAncPtr vCap + v) = oldCid :=
    (hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v hv_F1).1.trans holdCid_def.symm
  have hold_act : oldCid ∈ x1.activeCids := by
    have h := hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v hv_F1
    rw [h.1, ← holdCid_def] at h; exact h.2.1
  have holdCid_lt : oldCid < vCap := (hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 oldCid hold_act).1
  have hcs_m1 : mem1 (fCompSizeBase fAncPtr vCap + oldCid) = oldSize :=
    (hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 oldCid hold_act).2.2.2.2.1.trans holdSize_def.symm
  have hrCnt_m1 : mem1 (fAncPtr + fOffRCount) = rCnt := hFAnc1'.1.trans hrCnt_def.symm
  have hrCnt_lt_vc : rCnt < vCap := by
    have hsub : S₁.R ⊆ (Finset.range vCap).erase v' := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨fun hEq => hv'_not_R1 (hEq ▸ hy),
        Finset.mem_range.mpr (hdgF1'.2.1 y (hInv₁.RF_V_eq ▸ hInv₁.to_RF_spanning.2.2.1 hy))⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hv'_cap), Finset.card_range, ← hrCnt_def] at hc
    clear * - hc hv'_cap; omega
  have holdSize_lt_vc : oldSize < vCap := by
    have hcard := (hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 oldCid hold_act).2.2.2.2.2.2
    have hsub : (S₁.RF.F.V.filter fun u => S₁.RF.F.Connected u (x1.compRoot oldCid)) ⊆
        (Finset.range vCap).erase v' := by
      intro y hy
      have hyV := (Finset.mem_filter.mp hy).1
      exact Finset.mem_erase.mpr ⟨fun hEq => hv'_not_F1 (hEq ▸ hyV),
        Finset.mem_range.mpr (hdgF1'.2.1 y hyV)⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hv'_cap), Finset.card_range] at hc
    rw [holdSize_def]
    clear * - hc hcard hv'_cap; omega
  -- Phase 3..end: run the entire tail from `st1`
  -- Phase 3..end: run the entire tail from `st1`
  have htag_m1 : mem1 updPtr = tag := by
    have h0 := hupd_ag1 0 (by clear * - hlen_eq; omega)
    simpa only [Nat.add_zero] using h0.trans htag_m
  have hkt_m1 : mem1 (updPtr + 3) = kt :=
    (hupd_ag1 3 (by clear * - hlen_eq; omega)).trans hkt_m
  have hkh_m1 : mem1 (updPtr + 4) = kh :=
    (hupd_ag1 4 (by clear * - hlen_eq; omega)).trans hkh_m
  have hr1_lo : ∀ r ≤ 17, st1.regs r = st0.regs r := fun r hr => by
    rw [hregs1, Function.update_of_ne (by omega)]
  have hregs_st1 :
      st1.regs 0 = b ∧ st1.regs 1 = updPtr ∧ st1.regs 2 = vCap ∧ st1.regs 3 = eCap ∧
      st1.regs 4 = n0 ∧ st1.regs 5 = tM ∧ st1.regs 6 = dgGPtr ∧ st1.regs 7 = tPtr ∧
      st1.regs 8 = dgFPtr ∧ st1.regs 9 = fAncPtr ∧ st1.regs 10 = auxPtr ∧
      st1.regs 11 = v ∧ st1.regs 12 = v' ∧ st1.regs 13 = kt ∧ st1.regs 14 = kh ∧
      st1.regs 15 = origBase ∧ st1.regs 16 = isOrigBase ∧ st1.regs 17 = vOrig :=
    ⟨(hr1_lo 0 (by decide)).trans hr0_0, (hr1_lo 1 (by decide)).trans hr0_1,
     (hr1_lo 2 (by decide)).trans hr0_2, (hr1_lo 3 (by decide)).trans hr0_3,
     (hr1_lo 4 (by decide)).trans hr0_4, (hr1_lo 5 (by decide)).trans hr0_5,
     (hr1_lo 6 (by decide)).trans hr0_6, (hr1_lo 7 (by decide)).trans hr0_7,
     (hr1_lo 8 (by decide)).trans hr0_8, (hr1_lo 9 (by decide)).trans hr0_9,
     (hr1_lo 10 (by decide)).trans hr0_10, (hr1_lo 11 (by decide)).trans hr0_11,
     (hr1_lo 12 (by decide)).trans hr0_12, (hr1_lo 13 (by decide)).trans hr0_13,
     (hr1_lo 14 (by decide)).trans hr0_14, (hr1_lo 15 (by decide)).trans hr0_15,
     (hr1_lo 16 (by decide)).trans hr0_16, (hr1_lo 17 (by decide)).trans hr0_17⟩
  obtain ⟨st', c_t, x', hrun_t, hsame1', hrep', hfr_t, hc_t⟩ :=
    lsfSplitUpdate_tail hw16 hend_ltw hupd_ltw hdisj_upd hInv hu_valid hv'_cap hcan_t hcan_h
      htag_23 hlen_eq htag_m1 hkt_m1 hkh_m1 hsame1 hrep1_copy hUpdAt1 hupd_word1
      hrCnt_def holdCid_def holdSize_def hcid_m1 hold_act holdCid_lt hcs_m1 hrCnt_m1
      hrCnt_lt_vc holdSize_lt_vc hregs_st1 hDgUpdF hDgUpdG hBFS hTSplit
  have hb_off : ∀ k < lsfHdrSize, k < 2 ^ w ∧ b + k < 2 ^ w := fun k hk => by
    clear * - hk hb_hdr_ltw; omega
  have hu_off : ∀ k ≤ 4, k < 2 ^ w ∧ updPtr + k < 2 ^ w := fun k hk => by
    clear * - hk hupd_ltw hlen_eq hw16; omega
  have ha_off : ∀ k < auxHdrSize, k < 2 ^ w ∧ auxPtr + k < 2 ^ w := fun k hk => by
    clear * - hk haux_end_ltw hw16; dsimp only [auxSize, auxHdrSize] at haux_end_ltw hk; omega
  have horig_v : origBase + v < 2 ^ w := by clear * - horig_end_ltw hv_lt; omega
  have hrest_run : ∃ o st'' c_r,
      Runs w p ω
        (.call 18 idxAddRoot [.reg 0, .reg 17] ;;
         .assign 18 (.load (.bin .add (.reg 9) (.const fOffIsRootPtr))) ;;
         .assign 19 (.load (.bin .add (.reg 9) (.const fOffRListPtr))) ;;
         .assign 20 (.load (.bin .add (.reg 9) (.const fOffCompIdPtr))) ;;
         .assign 21 (.load (.bin .add (.reg 9) (.const fOffCompSizePtr))) ;;
         .assign 22 (.load (.bin .add (.reg 9) (.const fOffRCount))) ;;
         .assign 23 (.load (.bin .add (.reg 20) (.reg 11))) ;;
         .assign 24 (.load (.bin .add (.reg 21) (.reg 23))) ;;
         .call 25 idxDgUpd [.reg 8, .reg 1, .const 0] ;;
         .store (.bin .add (.reg 18) (.reg 12)) (.const 1) ;;
         .store (.bin .add (.reg 19) (.reg 22)) (.reg 12) ;;
         .store (.bin .add (.reg 9) (.const fOffRCount)) (.bin .add (.reg 22) (.const 1)) ;;
         .store (.bin .add (.reg 0) (.const lsfOffRCount)) (.bin .add (.reg 22) (.const 1)) ;;
         .store (.bin .add (.reg 20) (.reg 12)) (.reg 23) ;;
         .call 25 idxBFS
           [.reg 8, .reg 9, .reg 10, .reg 2,
            .bin .add (.bin .mul (.const 3) (.reg 3)) (.reg 4), .reg 4,
            .reg 11, .reg 12, .reg 23, .reg 11, .reg 12, .bin .add (.reg 24) (.const 1)] ;;
         .call 25 idxTSplit [.reg 7, .reg 1, .reg 2, .reg 3, .reg 5] ;;
         .call 25 idxDgUpd [.reg 6, .reg 1, .const 1] ;;
         .store (.bin .add (.reg 15) (.reg 12)) (.reg 17) ;;
         .store (.bin .add (.reg 16) (.reg 12)) (.const 0) ;;
         .ret (.bin .add (.bin .add (.const 5) (.reg 13)) (.reg 14)))
        st0 o st'' c_r ∧ (o = .returned len ∧ st'' = st') ∧ c_r ≤ c1 + c_t + 1 := by
    have h := runs_seq_of_runs_le' (k := 0) (T := c1 + c_t + 1)
      (Q := fun o st'' => o = .returned len ∧ st'' = st') hrun1
      ⟨.returned len, st', c_t, hrun_t, ⟨rfl, rfl⟩, by clear * -; omega⟩
    rcases h with ⟨o, st'', c_r, hrun, hQ, hc⟩
    exact ⟨o, st'', c_r, hrun, hQ, by clear * - hc; omega⟩
  obtain ⟨_, st'', c_all, hrun_all, ⟨rfl, hst⟩, hc_all⟩ :=
    lsfSplitUpdate_prefix hb_off hu_off ha_off horig_v
      hhdr.1 hhdr.2.1 hhdr.2.2.1 hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hhdr.2.2.2.2.1 hhdr.2.2.2.2.2.1 hhdr.2.2.2.2.2.2.1 hhdr.2.2.2.2.2.2.2.1
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hv_m hv'_m hkt_m hkh_m horig_ptr_m hisOrig_ptr_m hvOrig_m hrest_run
  refine ⟨st', c_all, x', hst ▸ hrun_all, hsame1.trans hsame1', hrep',
    fun a ha => (hfr_t a ha).trans ((hfr1 a ha).trans (hmem0 ▸ rfl)), ?_⟩
  dsimp only [st0, mem1, argsSize, Expr.size] at hc1 ⊢
  clear * - hc_all hc1 hc_t hlen_eq
  omega


end

end MinCostFlow.LSF.Program
