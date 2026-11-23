module

public import MinCostFlow.LSF.Program.BatchSplitOpPost
import Mathlib.Tactic.Linarith

/-!
# Post-`addOrigRoot` Execution Tail of `lsfSplitUpdateProc` (`BatchSplitOpTail`)

Verifies the post-`addOrigRoot` tail of `lsfSplitUpdateProc`: loading `fAnc` metadata, splitting
`dgF`, registering `v'` as a root, running `splitCompBFS`, updating `TBlock` and `dgG`, writing
`origVert[v']`/`isOrigVert[v']`, and assembling `(LSFRep h).rep` and the potential bound.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

set_option maxHeartbeats 1200000 in
lemma lsfSplitUpdate_tail
    {w h b updPtr v v' kt kh len tag idxDgUpd idxBFS idxTSplit rCnt oldCid oldSize : ℕ}
    {St Sh : Finset ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {x x1 : LSFConcrete} {st1 : State}
    (hw16 : 16 ≤ 2 ^ w) (hend_ltw : x.endAddr b < 2 ^ w) (hupd_ltw : updPtr + len < 2 ^ w)
    (hdisj_upd : ∀ i < len, updPtr + i < b ∨ x.endAddr b ≤ updPtr + i)
    (hInv : LSFStructInv S)
    (hu_valid : S.G.UpdateIsValid (.split v v' St Sh))
    (hv'_cap : v' < x.vCap)
    (hcan_t : ∀ e ∈ St, e ∈ S.G.E ∧ S.G.tail e = v)
    (hcan_h : ∀ e ∈ Sh, e ∈ S.G.E ∧ S.G.head e = v)
    (htag_23 : tag = 2 ∨ tag = 3) (hlen_eq : len = 5 + kt + kh)
    (htag_m1 : st1.mem updPtr = tag) (hkt_m1 : st1.mem (updPtr + 3) = kt)
    (hkh_m1 : st1.mem (updPtr + 4) = kh)
    (hsame1 : SameStaticConcrete x x1)
    (hrep1 : (LSFRep h).rep b { S with R₀_base := insert (S.origVert v) S.R₀_base } x1 st1.mem)
    (hUpdAt1 : UpdateAt st1.mem updPtr ({ S with R₀_base := insert (S.origVert v) S.R₀_base }).G
      (.split v v' St Sh) len)
    (hupd_word1 : ∀ i < len, st1.mem (updPtr + i) < 2 ^ w)
    (hrCnt_def : rCnt = ({ S with R₀_base := insert (S.origVert v) S.R₀_base }).R.card)
    (holdCid_def : oldCid = x1.compId v)
    (holdSize_def : oldSize = x1.compSize oldCid)
    (hcid_m1 : st1.mem (fCompIdBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap + v) = oldCid)
    (hold_act : oldCid ∈ x1.activeCids)
    (holdCid_lt : oldCid < x.vCap)
    (hcs_m1 : st1.mem (fCompSizeBase (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM) x.vCap + oldCid) = oldSize)
    (hrCnt_m1 : st1.mem (lsfFAncPtr b x.vCap x.eCap x.n0 x.tM + fOffRCount) = rCnt)
    (hrCnt_lt_vc : rCnt < x.vCap)
    (holdSize_lt_vc : oldSize < x.vCap)
    (hregs_st1 :
      st1.regs 0 = b ∧ st1.regs 1 = updPtr ∧ st1.regs 2 = x.vCap ∧ st1.regs 3 = x.eCap ∧
      st1.regs 4 = x.n0 ∧ st1.regs 5 = x.tM ∧ st1.regs 6 = lsfDgGPtr b ∧
      st1.regs 7 = lsfTBlockPtr b x.vCap x.eCap ∧ st1.regs 8 = lsfDgFPtr b x.vCap x.eCap x.tM ∧
      st1.regs 9 = lsfFAncPtr b x.vCap x.eCap x.n0 x.tM ∧
      st1.regs 10 = lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w ∧
      st1.regs 11 = v ∧ st1.regs 12 = v' ∧ st1.regs 13 = kt ∧ st1.regs 14 = kh ∧
      st1.regs 15 = auxOrigVertBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ∧
      st1.regs 16 = auxIsOrigVertBase (lsfAuxPtr b x.vCap x.eCap x.n0 x.tM x.L_w) x.vCap x.n0 ∧
      st1.regs 17 = S.origVert v)
    (hDgUpdF : ∀ G H, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x.vCap (fECap x.eCap x.n0) G H (.split v v' St Sh) len))
    (hDgUpdG : ∀ G, MeetsContract w p idxDgUpd
      (dgApplyUpdateContract w x.vCap x.eCap G G (.split v v' St Sh) len))
    (hBFS : ∀ F, MeetsContract w p idxBFS (splitCompBFSContract w F))
    (hTSplit : ∀ G T_cur, MeetsContract w p idxTSplit
      (lsfTBlockSplitContract w x.vCap x.eCap x.tM G T_cur S.T₀ S.π x.tOrigList v v' St Sh len)) :
    ∃ st' c_t x',
      Runs w p ω
        (.assign 18 (.load (.bin .add (.reg 9) (.const fOffIsRootPtr))) ;;
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
        st1 (.returned len) st' c_t ∧
      SameStaticConcrete x1 x' ∧
      (LSFRep h).rep b (applyLSFUpdate S (.split v v' St Sh)) x' st'.mem ∧
      (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = st1.mem a) ∧
      c_t + lsfPhi b x' st'.mem ≤ 2700 * len + 1000 + lsfPhi b x1 st1.mem := by
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
  set vOrig := S.origVert v
  set S₁ := { S with R₀_base := insert vOrig S.R₀_base }
  set S' := applyLSFUpdate S (.split v v' St Sh)
  set mem1 := st1.mem
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
  have hstep := applyLSFUpdate_split_step hInv hu_valid
  have hInv₁ : LSFStructInv S₁ := hstep.2.1
  have hInv' : LSFStructInv S' := hstep.2.2.1
  have hv_R1 : v ∈ S₁.R := hstep.2.2.2.2.1
  have hv_F1 : v ∈ S₁.RF.F.V := hInv₁.RF_V_eq ▸ hu_valid.1
  have hv'_not_R1 : v' ∉ S₁.R := hstep.2.2.2.2.2.1
  have hR' : S'.R = insert v' S₁.R := hstep.2.2.2.2.2.2.1
  have hFres_congr := hstep.2.2.2.2.2.2.2.1
  have hx1_vc : x1.vCap = vCap := hsame1.1
  have hx1_ec : x1.eCap = eCap := hsame1.2.1
  have hx1_n0 : x1.n0 = n0 := hsame1.2.2.1
  have hx1_tM : x1.tM = tM := hsame1.2.2.2.2.1
  have hx1_Lw : x1.L_w = L_w := hsame1.2.2.2.2.2.2.2.2.1
  have hx1_tL : x1.tOrigList = x.tOrigList := hsame1.2.2.2.2.2.2.2.2.2.2.1
  have hrep1_copy := hrep1
  rcases hrep1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdgG1, hT1, hdgF1, hFAnc1, _, _, hAux1⟩
  have hFAnc1' : FAncAt mem1 fAncPtr vCap S₁.RF x1.rList x1.compId x1.compRoot x1.compSize x1.activeCids := by
    simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM] using hFAnc1
  have hdgF1' : DynGraphAt mem1 dgFPtr vCap eCapF S₁.RF.F := by
    simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, eCapF] using hdgF1
  have hdgG1' : DynGraphAt mem1 dgGPtr vCap eCap S₁.G := by
    simpa only [hx1_vc, hx1_ec] using hdgG1
  have hT1' : TBlockAt mem1 tPtr vCap eCap tM S₁.G S₁.T_cur S.T₀ S.π x.tOrigList := by
    simpa only [hx1_vc, hx1_ec, hx1_tM, hx1_tL, tPtr] using hT1
  have hv_lt : v < vCap := hdgG1'.2.1 v hu_valid.1
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
  have hlen_ltw : len < 2 ^ w := by omega
  have horig_end_ltw : origBase + vCap < 2 ^ w := by clear * - haux_bds haux_end_ltw; omega
  have hisOrig_end_ltw : isOrigBase + vCap < 2 ^ w := by clear * - haux_bds haux_end_ltw; omega
  obtain ⟨mSmall, hmSmall_eq⟩ : ∃ mSmall : ℕ, mSmall = min
      (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card
      (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card := ⟨_, rfl⟩
  have hf_bases_ltw : fIsRootBase fAncPtr + vCap < 2 ^ w ∧
      fRListBase fAncPtr vCap + vCap < 2 ^ w ∧
      fCompIdBase fAncPtr vCap + vCap < 2 ^ w ∧
      fCompSizeBase fAncPtr vCap + vCap < 2 ^ w := by
    clear * - hfAnc_bds hfAnc_end_ltw; omega
  rcases hregs_st1 with ⟨h1_0, h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_7, h1_8, h1_9,
    h1_10, h1_11, h1_12, h1_13, h1_14, h1_15, h1_16, h1_17⟩
  have hmSmall_box : Unit → mSmall = min
      (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card
      (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card :=
    fun () => hmSmall_eq
  have hstep_box : Unit →
      S.origVert v ∈ S.T₀.V ∧ LSFStructInv S₁ ∧ LSFStructInv S' ∧ S'.R_orig = S₁.R_orig ∧
      v ∈ S₁.R ∧ v' ∉ S₁.R ∧ S'.R = insert v' S₁.R ∧
      ((S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E))).V = S'.RF.F.V ∧
       (S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E))).E = S'.RF.F.E ∧
       ∀ e ∈ (S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E))).E,
         (S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E))).tail e = S'.RF.F.tail e ∧
         (S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E))).head e = S'.RF.F.head e) ∧
      v ∈ S'.RF.F.V ∧ v' ∈ S'.RF.F.V ∧ ¬ S'.RF.F.Connected v v' ∧
      (∀ u ∈ S'.RF.F.V, (S'.RF.F.Connected u v ∨ S'.RF.F.Connected u v') ↔
        (u = v' ∨ (u ∈ S₁.RF.F.V ∧ S₁.RF.F.Connected u v))) ∧
      (∀ u ∈ S'.RF.F.V, ¬ S'.RF.F.Connected u v → ¬ S'.RF.F.Connected u v' →
        u ∈ S₁.RF.F.V ∧ ∀ w ∈ S₁.RF.F.V, S'.RF.F.Connected u w ↔ S₁.RF.F.Connected u w) ∧
      (∀ u ∈ S'.RF.F.V, ∀ w ∈ S'.RF.F.V,
        (S'.RF.F.Connected u v ∨ S'.RF.F.Connected u v') →
        ¬ S'.RF.F.Connected w v → ¬ S'.RF.F.Connected w v' →
        ¬ S'.RF.F.Connected u w) ∧
      ((S'.RF.F.Connected v v ∧ S'.RF.F.Connected v' v') ∨
        (S'.RF.F.Connected v v' ∧ S'.RF.F.Connected v' v)) ∧
      (S₁.RF.F.V.filter fun u => S₁.RF.F.Connected u v).card + 1 =
        (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v).card +
        (S'.RF.F.V.filter fun u => S'.RF.F.Connected u v').card :=
    fun () => hstep
  have hrCnt_box : Unit → rCnt = S₁.R.card := fun () => hrCnt_def
  have holdCid_box : Unit → oldCid = x1.compId v := fun () => holdCid_def
  have holdSize_box : Unit → oldSize = x1.compSize oldCid := fun () => holdSize_def
  clear hmSmall_eq hstep hrCnt_def holdCid_def holdSize_def
  suffices hgoal : ∃ o st' c_t,
      Runs w p ω
        (.assign 18 (.load (.bin .add (.reg 9) (.const fOffIsRootPtr))) ;;
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
        st1 o st' c_t ∧
      (o = .returned len ∧ ∃ x', SameStaticConcrete x1 x' ∧ (LSFRep h).rep b S' x' st'.mem ∧
        (∀ a, a < b ∨ x.endAddr b ≤ a → st'.mem a = mem1 a) ∧
        lsfPhi b x' st'.mem + 1100 * mSmall ≤ lsfPhi b x1 mem1) ∧
      0 + c_t ≤ 2700 * len + 1000 + 600 * mSmall by
    rcases hgoal with ⟨_, st', c_t, hr, ⟨rfl, x', hs, hrep', hfr', hphi_d⟩, hc⟩
    exact ⟨st', c_t, x', hr, hs, hrep', hfr', by omega⟩
  -- 7 loads from `fAncPtr`
  have heval_f : ∀ (st : State) (off : ℕ),
      st.regs 9 = fAncPtr → off < 6 →
      Expr.eval w st (.bin .add (.reg 9) (.const off)) = some (fAncPtr + off) := by
    intro st off h9 hoff
    have h1 : off < 2 ^ w := by clear * - hw16 hoff; omega
    have h2 : fAncPtr + off < 2 ^ w := by
      dsimp only [fAncSize, fAncHdrSize] at hfAnc_end_ltw; clear * - hfAnc_end_ltw hoff; omega
    simp only [Expr.eval, BinOp.eval, h9, h1, h2, ↓reduceIte]
  refine runs_seq_assign_le (v := fIsRootBase fAncPtr)
    (Expr.eval_load_of_eq (heval_f _ fOffIsRootPtr h1_9 (by decide)) hFAnc1'.2.1) ?_
  refine runs_seq_assign_le (v := fRListBase fAncPtr vCap)
    (Expr.eval_load_of_eq (heval_f _ fOffRListPtr
      (by dsimp only; rw [Function.update_of_ne (by decide)]; exact h1_9) (by decide)) hFAnc1'.2.2.1) ?_
  refine runs_seq_assign_le (v := fCompIdBase fAncPtr vCap)
    (Expr.eval_load_of_eq (heval_f _ fOffCompIdPtr
      (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h1_9)
      (by decide)) hFAnc1'.2.2.2.1) ?_
  refine runs_seq_assign_le (v := fCompSizeBase fAncPtr vCap)
    (Expr.eval_load_of_eq (heval_f _ fOffCompSizePtr
      (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact h1_9) (by decide)) hFAnc1'.2.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := rCnt)
    (Expr.eval_load_of_eq (heval_f _ fOffRCount
      (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact h1_9)
      (by decide)) hrCnt_m1) ?_
  refine runs_seq_assign_le (v := oldCid)
    (Expr.eval_load_of_eq (by
      have hlt : fCompIdBase fAncPtr vCap + v < 2 ^ w := by clear * - hf_bases_ltw hv_lt; omega
      simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (20 : ℕ) ≠ 22),
        Function.update_of_ne (by decide : (20 : ℕ) ≠ 21), Function.update_self,
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 22),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 21),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 20),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 19),
        Function.update_of_ne (by decide : (11 : ℕ) ≠ 18), h1_11, hlt, ↓reduceIte]) hcid_m1) ?_
  refine runs_seq_assign_le (v := oldSize)
    (Expr.eval_load_of_eq (by
      have hlt : fCompSizeBase fAncPtr vCap + oldCid < 2 ^ w := by
        clear * - hf_bases_ltw holdCid_lt; omega
      simp only [Expr.eval, BinOp.eval, Function.update_of_ne (by decide : (21 : ℕ) ≠ 23),
        Function.update_of_ne (by decide : (21 : ℕ) ≠ 22), Function.update_self,
        hlt, ↓reduceIte]) hcs_m1) ?_
  -- Register lookup helper after the 7 loads (regs 0..24 are untouched by `.call 25`)
  let rgA : ℕ → ℕ := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update st1.regs
      18 (fIsRootBase fAncPtr)) 19 (fRListBase fAncPtr vCap)) 20 (fCompIdBase fAncPtr vCap))
      21 (fCompSizeBase fAncPtr vCap)) 22 rCnt) 23 oldCid) 24 oldSize
  have hrgA_lo : ∀ r ≤ 17, rgA r = st1.regs r := fun r hr => by
    dsimp only [rgA]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hrgA_18 : rgA 18 = fIsRootBase fAncPtr := by dsimp only [rgA]; simp
  have hrgA_19 : rgA 19 = fRListBase fAncPtr vCap := by dsimp only [rgA]; simp
  have hrgA_20 : rgA 20 = fCompIdBase fAncPtr vCap := by dsimp only [rgA]; simp
  have hrgA_21 : rgA 21 = fCompSizeBase fAncPtr vCap := by dsimp only [rgA]; simp
  have hrgA_22 : rgA 22 = rCnt := by dsimp only [rgA]; simp
  have hrgA_23 : rgA 23 = oldCid := by dsimp only [rgA]; simp
  have hrgA_24 : rgA 24 = oldSize := by dsimp only [rgA]; simp
  have hupd25 : ∀ {rg : ℕ → ℕ} {ret : ℕ} (r : ℕ), r ≤ 24 → Function.update rg 25 ret r = rg r :=
    fun r hr => Function.update_of_ne (by clear * - hr; omega) _ _
  -- Call 1: dgApplyUpdate(dgFPtr, updPtr, 0)
  have hpre_dgF : (dgApplyUpdateContract w vCap eCapF S₁.G S₁.RF.F (.split v v' St Sh) len).pre
      [dgFPtr, updPtr, 0] mem1 :=
    ⟨dgFPtr, updPtr, 0, rfl, hw16, hdgF_end_ltw, hupd_ltw,
      fun i hi => by rcases hdisj_upd i hi with h | h <;> [left; right] <;>
        (clear * - h hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hend_eq; omega),
      hupd_word1, hUpdAt1, hu_valid, hv'_cap, hdgF1', Or.inr ⟨rfl, hInv₁.hF_sub_G, hInv₁.RF_V_eq⟩⟩
  refine runs_seq_call_le (hDgUpdF S₁.G S₁.RF.F)
    (by
      have h8 : rgA 8 = dgFPtr := (hrgA_lo 8 (by decide)).trans h1_8
      have h1 : rgA 1 = updPtr := (hrgA_lo 1 (by decide)).trans h1_1
      have h0w : 0 < 2 ^ w := by clear * - hw16; omega
      change evalArgs w { mem := mem1, regs := rgA, pos := st1.pos } [.reg 8, .reg 1, .const 0] =
        some [dgFPtr, updPtr, 0]
      simp only [evalArgs, Expr.eval, h8, h1, h0w, ↓reduceIte])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> (clear * - hw16 hdgF_end_ltw hupd_ltw; omega))
    hpre_dgF ?_
  intro ret_dgF mem2 pos2 hpost_dgF
  rcases hpost_dgF with ⟨_, _, _, hEq_dgF, _, hdgF2_raw, hfr_dgF⟩
  simp only [List.cons.injEq, and_true] at hEq_dgF
  rcases hEq_dgF with ⟨rfl, rfl, hmodeF⟩
  subst hmodeF
  have hdgF2 : DynGraphAt mem2 dgFPtr vCap eCapF S'.RF.F := by
    have hFres : dgBatchTarget 0 S₁.RF.F (.split v v' St Sh) =
        S₁.RF.F.applyUpdate (.split v v' (St ∩ S₁.RF.F.E) (Sh ∩ S₁.RF.F.E)) := rfl
    rw [hFres] at hdgF2_raw
    exact hdgF2_raw.congr_ends hFres_congr.1 hFres_congr.2.1 hFres_congr.2.2
  -- 5 stores on `fAnc` and `b.rCount`
  have hrgA_exp :
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update st1.regs
          18 (fIsRootBase fAncPtr)) 19 (fRListBase fAncPtr vCap)) 20 (fCompIdBase fAncPtr vCap))
          21 (fCompSizeBase fAncPtr vCap)) 22 rCnt) 23 oldCid) 24 oldSize = rgA := rfl
  have hrg2 : ∀ r ≤ 24,
      Function.update
        (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update st1.regs
            18 (fIsRootBase fAncPtr)) 19 (fRListBase fAncPtr vCap)) 20 (fCompIdBase fAncPtr vCap))
            21 (fCompSizeBase fAncPtr vCap)) 22 rCnt) 23 oldCid) 24 oldSize)
        25 ret_dgF r = rgA r := fun r hr => hupd25 r hr
  have h0w : 0 < 2 ^ w := by clear * - hw16; omega
  have h1w : 1 < 2 ^ w := by clear * - hw16; omega
  have h3w : 3 < 2 ^ w := by clear * - hw16; omega
  have h5w : 5 < 2 ^ w := by clear * - hw16; omega
  have hrc1_w : rCnt + 1 < 2 ^ w := by clear * - hrCnt_lt_vc hvCap_ltw; omega
  have hfz0 : fOffRCount < 2 ^ w := by dsimp [fOffRCount]; exact h0w
  have hlrc_w : lsfOffRCount < 2 ^ w := by
    dsimp only [lsfOffRCount, lsfHdrSize] at hb_hdr_ltw ⊢; clear * - hb_hdr_ltw; omega
  have hblrc_w : b + lsfOffRCount < 2 ^ w := by
    dsimp only [lsfOffRCount, lsfHdrSize] at hb_hdr_ltw ⊢; clear * - hb_hdr_ltw; omega
  refine runs_seq_store_le (x := fIsRootBase fAncPtr + v') (v := 1)
    (by have hlt : fIsRootBase fAncPtr + v' < 2 ^ w := by clear * - hf_bases_ltw hv'_cap; omega
        dsimp only
        simp only [Expr.eval, BinOp.eval, hrg2 18 (by decide), hrgA_18,
          hrg2 12 (by decide), hrgA_lo 12 (by decide), h1_12, hlt, ↓reduceIte])
    (by simp only [Expr.eval, h1w, ↓reduceIte]) ?_
  refine runs_seq_store_le (x := fRListBase fAncPtr vCap + rCnt) (v := v')
    (by have hlt : fRListBase fAncPtr vCap + rCnt < 2 ^ w := by clear * - hf_bases_ltw hrCnt_lt_vc; omega
        dsimp only
        simp only [Expr.eval, BinOp.eval, hrg2 19 (by decide), hrgA_19,
          hrg2 22 (by decide), hrgA_22, hlt, ↓reduceIte])
    (by dsimp only; simp only [Expr.eval, hrg2 12 (by decide), hrgA_lo 12 (by decide), h1_12]) ?_
  refine runs_seq_store_le (x := fAncPtr + fOffRCount) (v := rCnt + 1)
    (by have hlt : fAncPtr + fOffRCount < 2 ^ w := by
          dsimp only [fOffRCount, fAncSize, fAncHdrSize] at hfAnc_end_ltw ⊢; clear * - hfAnc_end_ltw; omega
        dsimp only
        simp only [Expr.eval, BinOp.eval, hrg2 9 (by decide), hrgA_lo 9 (by decide), h1_9,
          hfz0, hlt, ↓reduceIte])
    (by dsimp only; simp only [Expr.eval, BinOp.eval, hrg2 22 (by decide), hrgA_22, h1w, hrc1_w, ↓reduceIte]) ?_
  refine runs_seq_store_le (x := b + lsfOffRCount) (v := rCnt + 1)
    (by dsimp only
        simp only [Expr.eval, BinOp.eval, hrg2 0 (by decide), hrgA_lo 0 (by decide), h1_0,
          hlrc_w, hblrc_w, ↓reduceIte])
    (by dsimp only; simp only [Expr.eval, BinOp.eval, hrg2 22 (by decide), hrgA_22, h1w, hrc1_w, ↓reduceIte]) ?_
  refine runs_seq_store_le (x := fCompIdBase fAncPtr vCap + v') (v := oldCid)
    (by have hlt : fCompIdBase fAncPtr vCap + v' < 2 ^ w := by clear * - hf_bases_ltw hv'_cap; omega
        dsimp only
        simp only [Expr.eval, BinOp.eval, hrg2 20 (by decide), hrgA_20,
          hrg2 12 (by decide), hrgA_lo 12 (by decide), h1_12, hlt, ↓reduceIte])
    (by dsimp only; simp only [Expr.eval, hrg2 23 (by decide), hrgA_23]) ?_
  let mem3 : ℕ → ℕ := Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update mem2 (fIsRootBase fAncPtr + v') 1)
          (fRListBase fAncPtr vCap + rCnt) v')
        (fAncPtr + fOffRCount) (rCnt + 1))
      (b + lsfOffRCount) (rCnt + 1))
    (fCompIdBase fAncPtr vCap + v') oldCid
  have hmem3_out : ∀ a, a ≠ fIsRootBase fAncPtr + v' → a ≠ fRListBase fAncPtr vCap + rCnt →
      a ≠ fAncPtr + fOffRCount → a ≠ b + lsfOffRCount → a ≠ fCompIdBase fAncPtr vCap + v' →
      mem3 a = mem2 a := fun a h1 h2 h3 h4 h5 => by
    dsimp only [mem3]
    rw [Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3,
      Function.update_of_ne h2, Function.update_of_ne h1]
  have hdgF3 : DynGraphAt mem3 dgFPtr vCap eCapF S'.RF.F :=
    hdgF2.of_agree fun a ha1 ha2 => hmem3_out a
      (by clear * - ha2 hl4 hfAnc_bds; omega)
      (by clear * - ha2 hl4 hfAnc_bds; omega)
      (by clear * - ha2 hl4 hfAnc_bds; omega)
      (by dsimp only [lsfOffRCount]; clear * - ha1 hb_lt_dgF; omega)
      (by clear * - ha2 hl4 hfAnc_bds; omega)
  have hmem3_aux : ∀ a, auxPtr ≤ a → a < auxPtr + auxSize vCap n0 → mem3 a = mem1 a := fun a ha1 _ =>
    (hmem3_out a
      (by clear * - ha1 hl5 hl6 hfAnc_bds hv'_cap; omega)
      (by clear * - ha1 hl5 hl6 hfAnc_bds hrCnt_lt_vc; omega)
      (by clear * - ha1 hl5 hl6 hfAnc_bds; omega)
      (by dsimp only [lsfOffRCount]; clear * - ha1 hl4 hl5 hl6 hb_lt_dgF; omega)
      (by clear * - ha1 hl5 hl6 hfAnc_bds hv'_cap; omega)).trans
      (hfr_dgF a (Or.inr (by clear * - ha1 hl4 hl5 hl6; omega)))
  have hAux3_vis : ∀ u < vCap, mem3 (auxVisABase auxPtr vCap n0 + u) = 0 ∧
      mem3 (auxVisBBase auxPtr vCap n0 + u) = 0 := fun u hu => by
    have h1 := hAux1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 u (hx1_vc.symm ▸ hu)
    simp only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw] at h1
    rw [hmem3_aux _ (by clear * - haux_bds; omega) (by clear * - haux_bds hu; omega),
      hmem3_aux _ (by clear * - haux_bds; omega) (by clear * - haux_bds hu; omega)]
    exact h1
  have haux_hdr_m3 : ∀ off < auxHdrSize, mem3 (auxPtr + off) = mem1 (auxPtr + off) := fun off hoff =>
    hmem3_aux _ (Nat.le_add_right _ _) (by clear * - haux_bds hoff; omega)
  have hFAnc3_hdr : mem3 (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap ∧
      mem3 (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap ∧
      mem3 (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap := by
    have hhd_f : ∀ off, 1 ≤ off → off < fAncHdrSize → mem3 (fAncPtr + off) = mem1 (fAncPtr + off) := by
      intro off ho1 ho2
      have hlt_r : fAncPtr + off < fIsRootBase fAncPtr := by
        dsimp only [fIsRootBase]; clear * - ho2; omega
      exact (hmem3_out _ (by clear * - hlt_r; omega)
        (by clear * - hlt_r hfAnc_bds; omega)
        (by dsimp only [fOffRCount]; clear * - ho1; omega)
        (by dsimp only [lsfOffRCount]; clear * - hl4 hb_lt_dgF; omega)
        (by clear * - hlt_r hfAnc_bds; omega)).trans
        (hfr_dgF _ (Or.inr (by clear * - hl4; omega)))
    exact ⟨(hhd_f fOffCompIdPtr (by decide) (by decide)).trans hFAnc1'.2.2.2.1,
      (hhd_f fOffCompRootPtr (by decide) (by decide)).trans hFAnc1'.2.2.2.2.1,
      (hhd_f fOffCompSizePtr (by decide) (by decide)).trans hFAnc1'.2.2.2.2.2.1⟩
  -- Call 2: splitCompBFS
  have holdCid_ne_v' : oldCid ≠ v' := fun hEq =>
    hv'_not_R1 (hEq ▸ hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hold_act)
  have hpre_bfs : (splitCompBFSContract w S'.RF.F).pre
      [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, v, v', oldCid, v, v', oldSize + 1] mem3 := by
    refine ⟨dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, v, v', oldCid, v, v', oldSize + 1,
      rfl, hw16, hl4.le, by clear * - hl5 hl6; omega, haux_end_ltw,
      hInv'.to_RF_spanning.1, hdgF3,
      hFAnc3_hdr.1, hFAnc3_hdr.2.1, hFAnc3_hdr.2.2,
      (haux_hdr_m3 auxOffQBufAPtr (by decide)).trans (by simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw] using hAux1.2.2.2.2.2.2.2.2.2.2.2.1),
      (haux_hdr_m3 auxOffQBufBPtr (by decide)).trans (by simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw] using hAux1.2.2.2.2.2.2.2.2.2.2.2.2.1),
      (haux_hdr_m3 auxOffVisAPtr (by decide)).trans (by simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw] using hAux1.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
      (haux_hdr_m3 auxOffVisBPtr (by decide)).trans (by simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw] using hAux1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
      hAux3_vis,
      (hstep_box ()).2.2.2.2.2.2.2.2.1, (hstep_box ()).2.2.2.2.2.2.2.2.2.1, (hstep_box ()).2.2.2.2.2.2.2.2.2.2.1,
      holdCid_lt, hv_lt, hv'_cap, holdCid_ne_v',
      (hstep_box ()).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
    have hsum_eq := (hstep_box ()).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hcard := (hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 oldCid hold_act).2.2.2.2.2.2
    have hcr_v : x1.compRoot oldCid = v := by
      have hcv := hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v hv_F1
      rw [hcv.1, ← holdCid_box ()] at hcv
      have hr_R := (hFAnc1'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 oldCid hold_act).2.2.1
      by_contra hne
      obtain ⟨r, _, huniq⟩ := hInv₁.to_RF_spanning.2.2.2.1 (x1.compRoot oldCid)
        (hInv₁.to_RF_spanning.2.2.1 hr_R)
      exact hne ((huniq _ ⟨hr_R, connected_refl _ _⟩).trans
        (huniq v ⟨hv_R1, connected_symm hcv.2.2⟩).symm)
    rw [hcr_v] at hcard
    rw [holdSize_box (), hcard, hsum_eq]
  refine runs_seq_call_le (hBFS S'.RF.F)
    (by
      have h3e : 3 * eCap + n0 = eCapF := rfl
      have hos1 : oldSize + 1 < 2 ^ w := by clear * - holdSize_lt_vc hvCap_ltw; omega
      dsimp only
      simp only [evalArgs, Expr.eval, BinOp.eval, hrg2 8 (by decide), hrg2 9 (by decide),
        hrg2 10 (by decide), hrg2 2 (by decide), hrg2 3 (by decide), hrg2 4 (by decide),
        hrg2 11 (by decide), hrg2 12 (by decide), hrg2 23 (by decide), hrg2 24 (by decide),
        hrgA_lo 8 (by decide), hrgA_lo 9 (by decide), hrgA_lo 10 (by decide),
        hrgA_lo 2 (by decide), hrgA_lo 3 (by decide), hrgA_lo 4 (by decide),
        hrgA_lo 11 (by decide), hrgA_lo 12 (by decide), hrgA_23, hrgA_24,
        h1_8, h1_9, h1_10, h1_2, h1_3, h1_4, h1_11, h1_12, h3w, h1w, h3eCap_ltw,
        h3e, heCapF_ltw, hos1, ↓reduceIte])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (clear * - hdgF_end_ltw hfAnc_end_ltw haux_end_ltw hvCap_ltw heCapF_ltw hn0_ltw
            hv_ltw hv'_ltw holdCid_lt holdSize_lt_vc; omega))
    hpre_bfs ?_
  intro ret_bfs mem4 pos4 hpost_bfs
  have hpost_bfs_copy := hpost_bfs
  rcases hpost_bfs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hEq_bfs, hret_bfs, hfr_bfs, _⟩
  simp only [List.cons.injEq, and_true] at hEq_bfs
  rcases hEq_bfs with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  subst hret_bfs
  have hVis4 : ∀ u < vCap, mem4 (auxVisABase auxPtr vCap n0 + u) = 0 ∧
      mem4 (auxVisBBase auxPtr vCap n0 + u) = 0 := fun u hu => by
    have hA := hfr_bfs (auxVisABase auxPtr vCap n0 + u)
      (fun ⟨_, h2⟩ => by clear * - h2 hl5 hl6 hfAnc_bds haux_bds; omega)
      (fun ⟨_, h2⟩ => by clear * - h2 haux_bds; omega)
    have hB := hfr_bfs (auxVisBBase auxPtr vCap n0 + u)
      (fun ⟨_, h2⟩ => by clear * - h2 hl5 hl6 hfAnc_bds haux_bds; omega)
      (fun ⟨_, h2⟩ => by clear * - h2 haux_bds; omega)
    rw [hA, hB]; exact hAux3_vis u hu
  -- Build `x'` and `phi_drop_split` via `split_post_fanc_and_phi`
  obtain ⟨compId', compRoot', compSize', hsame1', hFAnc4_raw, hphi_drop⟩ :=
    split_post_fanc_and_phi (mem3 := mem3) (mem4 := mem4) hInv hu_valid (hx1_vc.symm ▸ hv'_cap) hrep1_copy
      (holdCid_box ()).symm (holdSize_box ()).symm
      (by simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM] using hfr_dgF)
      (by dsimp only [mem3]; simp only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hrCnt_box (), fAncPtr]; rfl)
      (by simpa only [hx1_vc, hx1_ec, hx1_n0, hx1_tM, hx1_Lw, eCapF, dgFPtr, fAncPtr, auxPtr]
        using hpost_bfs_copy)
  have hphi_box : Unit → (500 * auxLogCap x1.n0 * (x1.n0 - S'.R_orig.card) + 1400 * S'.RF.F.E.card +
      1100 * ∑ e ∈ S'.RF.F.E, Nat.log 2 (max 1 (compSize' (compId' (S'.RF.F.tail e)) - 1))) +
      1100 * min (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v).card
        (S'.RF.F.E.filter fun e => S'.RF.F.Connected (S'.RF.F.tail e) v').card ≤
      lsfPhi b x1 mem1 := fun () => hphi_drop
  clear hpost_bfs_copy hphi_drop hpre_bfs hpre_dgF hFAnc3_hdr haux_hdr_m3 hAux3_vis hFAnc1' hdgF1'
  let x' : LSFConcrete :=
    { x1 with
      rList := x1.rList ++ [v']
      compId := compId'
      compRoot := compRoot'
      compSize := compSize'
      activeCids := insert v' x1.activeCids }
  -- mem4 outside `[fCompIdBase, fCompSizeBase + vCap) ∪ [auxQBufABase, auxQBufBBase + vCap)` equals mem3
  have hfr_bfs_below_cid : ∀ a, a < fCompIdBase fAncPtr vCap → mem4 a = mem3 a := fun a ha =>
    hfr_bfs a (fun ⟨h1, _⟩ => by clear * - ha h1; omega)
      (fun ⟨h1, _⟩ => by clear * - ha h1 hl5 hl6 hfAnc_bds haux_bds; omega)
  have hmem4_out_b : ∀ a, a < b ∨ x.endAddr b ≤ a → mem4 a = mem1 a := fun a ha => by
    have h43 : mem4 a = mem3 a := hfr_bfs a
      (fun ⟨h1, h2⟩ => by clear * - ha h1 h2 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hfAnc_bds hend_eq; rcases ha with h | h <;> omega)
      (fun ⟨h1, h2⟩ => by clear * - ha h1 h2 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 haux_bds hend_eq; rcases ha with h | h <;> omega)
    have h32 : mem3 a = mem2 a := hmem3_out a
      (by clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hfAnc_bds hv'_cap hend_eq; rcases ha with h | h <;> omega)
      (by clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hfAnc_bds hrCnt_lt_vc hend_eq; rcases ha with h | h <;> omega)
      (by clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hfAnc_bds hend_eq; rcases ha with h | h <;> omega)
      (by dsimp only [lsfOffRCount]; clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hb_lt_dgF hend_eq; rcases ha with h | h <;> omega)
      (by clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hfAnc_bds hv'_cap hend_eq; rcases ha with h | h <;> omega)
    exact h43.trans (h32.trans (hfr_dgF a (by
      clear * - ha hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hend_eq; rcases ha with h | h <;> [left; right] <;> omega)))
  have hupd_ag4 : ∀ i < len, mem4 (updPtr + i) = mem1 (updPtr + i) := fun i hi =>
    hmem4_out_b _ (hdisj_upd i hi)
  have hUpdAt4 : UpdateAt mem4 updPtr S₁.G (.split v v' St Sh) len :=
    UpdateAt.of_agree hUpdAt1 hupd_ag4
  have hupd_word4 : ∀ i < len, mem4 (updPtr + i) < 2 ^ w := fun i hi => by
    rw [hupd_ag4 i hi]; exact hupd_word1 i hi
  have hT4_pre : TBlockAt mem4 tPtr vCap eCap tM S₁.G S₁.T_cur S.T₀ S.π x.tOrigList :=
    hT1'.of_agree fun a ha1 ha2 => by
      have h43 := hfr_bfs_below_cid a (by clear * - ha2 hl3 hl4 hfAnc_bds; omega)
      have h32 := hmem3_out a
        (by clear * - ha2 hl3 hl4 hfAnc_bds; omega)
        (by clear * - ha2 hl3 hl4 hfAnc_bds; omega)
        (by clear * - ha2 hl3 hl4 hfAnc_bds; omega)
        (by dsimp only [lsfOffRCount, lsfHdrSize] at hl1 ⊢; clear * - ha1 hl1 hl2; omega)
        (by clear * - ha2 hl3 hl4 hfAnc_bds; omega)
      exact h43.trans (h32.trans (hfr_dgF a (Or.inl (by clear * - ha2 hl3; omega))))
  -- Call 3: lsfTBlockSplit(tPtr, updPtr, vCap, eCap, tM)
  have hpre_tSplit : (lsfTBlockSplitContract w vCap eCap tM S₁.G S₁.T_cur S.T₀ S.π x.tOrigList
      v v' St Sh len).pre [tPtr, updPtr, vCap, eCap, tM] mem4 :=
    ⟨tPtr, updPtr, rfl, hw16, htPtr_end_ltw, hupd_ltw,
      fun i hi => by rcases hdisj_upd i hi with h | h <;> [left; right] <;>
        (clear * - h hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hend_eq; omega),
      hupd_word4, hInv₁.hG_val, hdgG1'.2.2.1, hu_valid, hv'_cap, hcan_t, hcan_h, hUpdAt4,
      hInv₁.hT_cur_forest.1, hInv₁.hT_cur_V, hInv₁.hT_cur_E, hT4_pre⟩
  refine runs_seq_call_le (hTSplit S₁.G S₁.T_cur)
    (by
      simp only [evalArgs, Expr.eval, hupd25 7 (by decide), hupd25 1 (by decide),
        hupd25 2 (by decide), hupd25 3 (by decide), hupd25 5 (by decide), hrgA_exp,
        hrgA_lo 7 (by decide), hrgA_lo 1 (by decide), hrgA_lo 2 (by decide), hrgA_lo 3 (by decide),
        hrgA_lo 5 (by decide), h1_7, h1_1, h1_2, h1_3, h1_5])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;>
          (clear * - htPtr_end_ltw hupd_ltw hvCap_ltw heCap_ltw htM_ltw; omega))
    hpre_tSplit ?_
  intro ret_ts mem5 pos5 hpost_ts
  rcases hpost_ts with ⟨_, _, hEq_ts, _, hT5_raw, hfr_ts⟩
  dsimp only at hfr_ts
  simp only [List.cons.injEq, and_true] at hEq_ts
  rcases hEq_ts with ⟨rfl, rfl, _, _, _⟩
  have hupd_ag5 : ∀ i < len, mem5 (updPtr + i) = mem4 (updPtr + i) := fun i hi =>
    hfr_ts _ (by rcases hdisj_upd i hi with h | h <;> [left; right] <;>
      (clear * - h hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hend_eq; omega))
  have hUpdAt5 : UpdateAt mem5 updPtr S₁.G (.split v v' St Sh) len :=
    UpdateAt.of_agree hUpdAt4 hupd_ag5
  have hupd_word5 : ∀ i < len, mem5 (updPtr + i) < 2 ^ w := fun i hi => by
    rw [hupd_ag5 i hi]; exact hupd_word4 i hi
  have hdgG5_pre : DynGraphAt mem5 dgGPtr vCap eCap S₁.G :=
    hdgG1'.of_agree fun a ha1 ha2 => by
      have h54 := hfr_ts a (Or.inl (by clear * - ha2 hl2; omega))
      have h43 := hfr_bfs_below_cid a (by clear * - ha2 hl2 hl3 hl4 hfAnc_bds; omega)
      have h32 := hmem3_out a
        (by clear * - ha2 hl2 hl3 hl4 hfAnc_bds; omega)
        (by clear * - ha2 hl2 hl3 hl4 hfAnc_bds; omega)
        (by clear * - ha2 hl2 hl3 hl4 hfAnc_bds; omega)
        (by dsimp only [lsfOffRCount, lsfHdrSize] at hl1 ⊢; clear * - ha1 hl1; omega)
        (by clear * - ha2 hl2 hl3 hl4 hfAnc_bds; omega)
      exact h54.trans (h43.trans (h32.trans (hfr_dgF a (Or.inl (by clear * - ha2 hl2 hl3; omega)))))
  -- Call 4: dgApplyUpdate(dgGPtr, updPtr, 1)
  have hpre_dgG : (dgApplyUpdateContract w vCap eCap S₁.G S₁.G (.split v v' St Sh) len).pre
      [dgGPtr, updPtr, 1] mem5 :=
    ⟨dgGPtr, updPtr, 1, rfl, hw16, hdgG_end_ltw, hupd_ltw,
      fun i hi => by rcases hdisj_upd i hi with h | h <;> [left; right] <;>
        (clear * - h hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hend_eq; omega),
      hupd_word5, hUpdAt5, hu_valid, hv'_cap, hdgG5_pre, Or.inl ⟨by decide, rfl⟩⟩
  refine runs_seq_call_le (hDgUpdG S₁.G)
    (by
      simp only [evalArgs, Expr.eval, hupd25 6 (by decide), hupd25 1 (by decide),
        hrgA_exp, hrgA_lo 6 (by decide), hrgA_lo 1 (by decide),
        h1_6, h1_1, h1w, ↓reduceIte])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> (clear * - hdgG_end_ltw hupd_ltw hw16; omega))
    hpre_dgG ?_
  intro ret_dgG mem6 pos6 hpost_dgG
  rcases hpost_dgG with ⟨_, _, _, hEq_dgG, _, hdgG6_raw, hfr_dgG⟩
  dsimp only at hfr_dgG
  simp only [List.cons.injEq, and_true] at hEq_dgG
  rcases hEq_dgG with ⟨rfl, rfl, hmodeG⟩
  subst hmodeG
  -- Final 2 stores on `origVert[v'] := vOrig` and `isOrigVert[v'] := 0`, and return `5 + kt + kh`
  refine runs_seq_store_le (x := origBase + v') (v := vOrig)
    (by have hlt : origBase + v' < 2 ^ w := by clear * - horig_end_ltw hv'_cap; omega
        simp only [Expr.eval, BinOp.eval, hupd25 15 (by decide), hupd25 12 (by decide),
          hrgA_exp, hrgA_lo 15 (by decide), hrgA_lo 12 (by decide),
          h1_15, h1_12, hlt, ↓reduceIte])
    (by simp only [Expr.eval, hupd25 17 (by decide), hrgA_exp,
          hrgA_lo 17 (by decide), h1_17]) ?_
  refine runs_seq_store_le (x := isOrigBase + v') (v := 0)
    (by have hlt : isOrigBase + v' < 2 ^ w := by clear * - hisOrig_end_ltw hv'_cap; omega
        simp only [Expr.eval, BinOp.eval, hupd25 16 (by decide), hupd25 12 (by decide),
          hrgA_exp, hrgA_lo 16 (by decide), hrgA_lo 12 (by decide),
          h1_16, h1_12, hlt, ↓reduceIte])
    (by simp only [Expr.eval, h0w, ↓reduceIte]) ?_
  let mem7 : ℕ → ℕ := Function.update (Function.update mem6 (origBase + v') vOrig) (isOrigBase + v') 0
  have h3v_rcnt : mem3 (b + lsfOffRCount) = rCnt + 1 := by
    have hlt_hdr : lsfOffRCount < lsfHdrSize := by decide
    dsimp only [mem3]
    rw [Function.update_of_ne (by clear * - hlt_hdr hl1 hl2 hl3 hl4 hfAnc_bds; omega),
      Function.update_self]
  have hdgG6_S' : DynGraphAt mem6 dgGPtr vCap eCap S'.G := by
    simpa only [dgBatchTarget, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, S', applyLSFUpdate] using hdgG6_raw
  have hv'_not_T0 : v' ∉ S'.T₀.V := fun h => hu_valid.2.1 (hInv.hGV_eq ▸ Finset.mem_union_left _ h)
  obtain ⟨hrep7, hfr_all7⟩ :=
    lsfSplitUpdate_assemble_rep (S := S) (x := x) (x1 := x1)
      (mem1 := mem1) (mem2 := mem2) (mem3 := mem3) (mem4 := mem4) (mem5 := mem5) (mem6 := mem6)
      hsame1 hrep1_copy hInv' hv'_not_R1 hR' hv'_not_T0 hv'_cap
      (hrCnt_box ()) hrCnt_lt_vc hfr_dgF hmem3_out h3v_rcnt hmem3_aux hfr_bfs hfr_bfs_below_cid
      hmem4_out_b hfr_ts hfr_dgG hdgG6_S' hT5_raw hdgF3 hFAnc4_raw hVis4
  have hphi7 : lsfPhi b x' mem7 + 1100 * mSmall ≤ lsfPhi b x1 mem1 := by
    rw [lsfPhi_eq_semantic hrep7, hmSmall_box ()]; exact hphi_box ()
  refine runs_ret_le (v := len)
    (by
      have h5kt : 5 + kt < 2 ^ w := by clear * - hlen_eq hlen_ltw; omega
      have h5ktkh : 5 + kt + kh = len := by clear * - hlen_eq; omega
      simp only [Expr.eval, BinOp.eval, hupd25 13 (by decide), hupd25 14 (by decide),
        hrgA_exp, hrgA_lo 13 (by decide), hrgA_lo 14 (by decide),
        h1_13, h1_14, h5w, h5kt, h5ktkh, hlen_ltw, ↓reduceIte])
    ⟨rfl, x', hsame1', hrep7, hfr_all7, hphi7⟩ ?_
  have h0_4 : mem4 updPtr = mem1 updPtr := by
    simpa only [Nat.add_zero] using hupd_ag4 0 (by clear * - hlen_eq; omega)
  have h0_5 : mem5 updPtr = mem4 updPtr := by
    simpa only [Nat.add_zero] using hupd_ag5 0 (by clear * - hlen_eq; omega)
  have hlen_m1 : dgUpdateMemLen mem1 updPtr = len := by
    dsimp only [dgUpdateMemLen]
    rw [htag_m1, hkt_m1, hkh_m1]
    rcases htag_23 with rfl | rfl <;> simp [hlen_eq]
  have hlen_m5 : dgUpdateMemLen mem5 updPtr = len := by
    dsimp only [dgUpdateMemLen]
    rw [h0_5, h0_4, htag_m1,
      hupd_ag5 3 (by clear * - hlen_eq; omega), hupd_ag4 3 (by clear * - hlen_eq; omega), hkt_m1,
      hupd_ag5 4 (by clear * - hlen_eq; omega), hupd_ag4 4 (by clear * - hlen_eq; omega), hkh_m1]
    rcases htag_23 with rfl | rfl <;> simp [hlen_eq]
  have hkt4 : mem4 (updPtr + 3) = kt :=
    (hupd_ag4 3 (by clear * - hlen_eq; omega)).trans hkt_m1
  have hkh4 : mem4 (updPtr + 4) = kh :=
    (hupd_ag4 4 (by clear * - hlen_eq; omega)).trans hkh_m1
  dsimp only [dgApplyUpdateContract, splitCompBFSContract, lsfTBlockSplitContract,
    List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    argsSize, Expr.size]
  rw [hlen_m1, hlen_m5, hkt4, hkh4, ← hmSmall_box ()]
  clear * - hlen_eq
  omega

end

end MinCostFlow.LSF.Program
