module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepCases

import Mathlib.Tactic

/-!
# Small-side and release-consumer tail for `asmFirstTourBlockStepStmt` (`AssemblyFirstTourStepTail`)

Verifies the shared small-side + release-consumer tail and the two wall iterations of
`asmFirstTourBlockStepStmt`:
1. `tourBlock_smallSide_and_rel_runs`: `outIdxSmallSide`, `statePtr` update, and `fConsumeRel`.
2. `tourBlock_case_forestDel_runs`: wall forest `.delete e` (`isOpen = 0`), popping the split entry,
   running `tourOp 1` (`cut`), `tourOp 0` (`dropEdge e`), and the shared tail.
3. `tourBlock_case_split_runs`: wall `.split v v' St Sh`, running `fApplyMove`, popping the split
   entry, reading `isRoot[v']`, running `tourOp 3` (`changeRoot`), and the shared tail.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

public section

/-- Frame congruence for `SplitEntriesAt`. -/
theorem asmFirstSplitEntriesAt_congr {mem mem' : ℕ → ℕ} {spPtr : ℕ}
    {L : List CompSplitEntry}
    (h : SplitEntriesAt mem spPtr L)
    (hag : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → mem' a = mem a) :
    SplitEntriesAt mem' spPtr L :=
  ⟨(hag spPtr (le_refl _) (by omega)).trans h.1, fun i hi =>
    let he := h.2 i hi
    ⟨(hag _ (by omega) (by omega)).trans he.1,
     (hag _ (by omega) (by omega)).trans he.2.1,
     (hag _ (by omega) (by omega)).trans he.2.2.1,
     (hag _ (by omega) (by omega)).trans he.2.2.2⟩⟩

/-! ## 1. Shared small-side + release-consumer tail -/

/-- Shared tail of forest-delete and vertex-split iterations: runs `outIdxSmallSide`, updates
`statePtr + 1` (if zero) and `statePtr + 2`, and calls `fConsumeRel`. -/
theorem tourBlock_smallSide_and_rel_runs
    {w vCap eCap bSelf bTour bOut tourH spPtr statePtr h2 spIdx splitPtr last kept fresh : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpRel : p.procs[bSelf + 0]? = some (asmFirstTourConsumeRelStmt (tourOp bTour 1) (outIdxSmallSide bOut)))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {sPrev sWall s_f : TourAbs} {tx2 : (tourAsmRep vCap eCap).τ} {st : State}
    {L relL spRest : List CompSplitEntry}
    {keep M E₀ St Sh : Finset ℕ} {G₀ S_cur S_f : MGraph}
    {P_done P_rel : List Update} {Ys_done : List (List End)}
    (hr0 : st.regs 0 = tourH) (hr5 : st.regs 5 = spPtr) (hr7 : st.regs 7 = statePtr)
    (hr9 : st.regs 9 = h2) (hr10 : st.regs 10 = L.length)
    (hr24 : st.regs 24 = kept) (hr25 : st.regs 25 = fresh)
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour sWall) tx2 st.mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a → a < h2)
    (hzero : ZeroFrom st.mem h2)
    (hspAt : SplitEntriesAt st.mem spPtr L) (hsp_le : spPtr + 1 + 4 * L.length ≤ h2)
    (hsp_disj : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → ¬ (tourAsmRep vCap eCap).foot tourH tx2 a)
    (hst_mem : st.mem statePtr = spIdx + 1 ∧ st.mem (statePtr + 1) = splitPtr ∧ st.mem (statePtr + 2) = last)
    (hst_le : statePtr + 3 ≤ h2)
    (hst_disj_foot : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx2 (statePtr + i))
    (hst_disj_sp : statePtr + 3 ≤ spPtr ∨ spPtr + 1 + 4 * L.length ≤ statePtr)
    (hst_disj_last : last = 0 ∨ last + 4 < statePtr ∨ statePtr + 3 ≤ last + 4)
    (hsp_disj_last : last = 0 ∨ last + 4 < spPtr ∨ spPtr + 1 + 4 * L.length ≤ last + 4)
    (hspIdx_le : spIdx + 1 ≤ L.length) (hdrop : L.drop (spIdx + 1) = relL ++ spRest)
    (hrest_stop : ∀ e rest, spRest = e :: rest → e.isRelease = false)
    (hkeptLt : kept < vCap) (hfreshLt : fresh < vCap)
    (hkeptR : kept ∈ sPrev.rf.R) (hfreshNotR : fresh ∉ sPrev.rf.R)
    (hR' : sWall.rf.R = insert fresh sPrev.rf.R)
    (hother : ∀ r ∈ sPrev.rf.R, r ≠ kept →
      (tourMarkedList sWall r).toFinset = (tourMarkedList sPrev r).toFinset)
    (hunion : (tourMarkedList sWall kept).toFinset ∪ (tourMarkedList sWall fresh).toFinset =
      (tourMarkedList sPrev kept).toFinset)
    (hM : TourMarksAt sWall M) (hkM : keep ⊆ M) (hME₀ : M ⊆ E₀)
    (hK : TourKeepMatch keep sWall (S_cur.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))))
    (hpre : OutSplitPrefixAt st.mem splitPtr last h2
      (fun a => (tourAsmRep vCap eCap).foot tourH tx2 a ∨ a < statePtr + 3)
      keep E₀ G₀ P_done S_cur Ys_done)
    (hchain : TourRelChain vCap eCap keep M sWall
      (S_cur.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))) relL P_rel s_f S_f)
    (hroom : h2 + outSmallSideSpace tourOutSpec (2 * eCap) +
      relL.length * tourSplitStepSpace eCap + 2 < 2 ^ w) :
    ∃ hEnd stF cTail txF splitPtrF lastF Y YsRel,
      Runs w p ω
        (.assign 26 (.reg 9) ;;
         .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
         .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
         .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
           (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
           .nop ;;
         .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
         .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
        st .normal stF cTail ∧
      stF.regs 9 = hEnd ∧
      (∀ r, r ≠ 9 → r ≠ 26 → r ≠ 27 → stF.regs r = st.regs r) ∧
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s_f) txF stF.mem ∧
      TourMarksAt s_f M ∧ TourKeepMatch keep s_f S_f ∧
      stF.mem statePtr = spIdx + 1 + relL.length ∧
      stF.mem (statePtr + 1) = splitPtrF ∧ stF.mem (statePtr + 2) = lastF ∧ h2 ≤ lastF ∧
      OutSplitPrefixAt stF.mem splitPtrF lastF hEnd
        (fun a => (tourAsmRep vCap eCap).foot tourH txF a ∨ a < statePtr + 3)
        keep E₀ G₀ (P_done ++ .split kept fresh (St ∩ keep) (Sh ∩ keep) :: P_rel) S_f
        (Ys_done ++ Y :: YsRel) ∧
      Y.length + (YsRel.map List.length).sum + tourMarkPot keep s_f ≤
        S_cur.batchEnc (.split kept fresh (St ∩ keep) (Sh ∩ keep) :: P_rel) +
          tourMarkPot keep sPrev ∧
      h2 + 5 ≤ hEnd ∧
      hEnd ≤ h2 + outSmallSideSpace tourOutSpec (2 * eCap) + relL.length * tourSplitStepSpace eCap ∧
      ZeroFrom stF.mem hEnd ∧
      (∀ a < h2, ¬ (tourAsmRep vCap eCap).foot tourH tx2 a →
        (a < statePtr ∨ statePtr + 3 ≤ a) → (last = 0 ∨ a ≠ last + 4) → stF.mem a = st.mem a) ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH txF a →
        (tourAsmRep vCap eCap).foot tourH tx2 a ∨ (h2 ≤ a ∧ a < hEnd)) ∧
      cTail + (tourAsmRep vCap eCap).phi tourH txF stF.mem ≤
        (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) *
          (Y.length + (YsRel.map List.length).sum + (1 + relL.length) + 1) * ordStoreLog eCap +
          (tourAsmRep vCap eCap).phi tourH tx2 st.mem := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH sWall tx2 st.mem at hrep
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hord_le : ordHandleOf tourH vCap eCap ≤ h2 := hrep.fixed_le_heap hfoot
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by omega : h2 + 1 < 2 ^ w)).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx2)) (by omega)
  have hh2_pos : 0 < h2 := lt_of_le_of_lt (Nat.zero_le _) (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx2))
  have hlast_ok : last = 0 ∨ (last + 4 < h2 ∧ ¬ (tourAsmRep vCap eCap).foot tourH tx2 (last + 4)) := by
    by_cases hP : P_done = []
    · exact Or.inl (hpre.2.1 hP).2.1
    · obtain ⟨_, _, hl5, hlav, _⟩ := hpre.2.2.1 hP
      exact Or.inr ⟨by omega, fun hf => hlav (Or.inl hf)⟩
  set r1 := Function.update st.regs 26 h2
  set r2 := Function.update r1 27 last
  have ha26 : Runs w p ω (.assign 26 (.reg 9)) st .normal { st with regs := r1 } 2 :=
    runs_assign_iff.mpr ⟨h2, Expr.eval_reg_of_eq hr9, rfl, rfl, rfl⟩
  have ha27 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 7) (.const 2))))
      { st with regs := r1 } .normal { st with regs := r2 } 5 :=
    runs_assign_iff.mpr ⟨last, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, hr7])) (Expr.eval_const (by omega)) (by omega))
      hst_mem.2.2, rfl, rfl, rfl⟩
  let T := tourPinnedOutAt w vCap eCap p bTour hpT sWall.ord sWall.rf
  set sOut : OutTourAbs := ⟨coreTour sWall.ord sWall.rf, sWall.marked⟩
  have hndK : (sOut.cord kept).Nodup := by
    by_cases hr : kept ∈ sWall.rf.R
    · show (coreTour sWall.ord sWall.rf kept).Nodup
      rw [← fullTour_filter_open sWall.ord hrep.valid.compat.forest hr]
      exact (fullTour_spec hrep.valid.compat kept).1.filter _
    · simp [sOut, coreTour, hr]
  have hndF : (sOut.cord fresh).Nodup := by
    by_cases hr : fresh ∈ sWall.rf.R
    · show (coreTour sWall.ord sWall.rf fresh).Nodup
      rw [← fullTour_filter_open sWall.ord hrep.valid.compat.forest hr]
      exact (fullTour_spec hrep.valid.compat fresh).1.filter _
    · simp [sOut, coreTour, hr]
  have hml_lt : ∀ x ∈ sOut.markedList kept ++ sOut.markedList fresh, x.1 < eCap := by
    intro x hx
    have hmem : x ∈ tourMarkedList sWall kept ∨ x ∈ tourMarkedList sWall fresh := by
      simpa [sOut, OutTourAbs.markedList, tourMarkedList] using hx
    rcases hmem with h1 | h2'
    · obtain ⟨_, ⟨u, hu⟩, _, _, _⟩ := (mem_tourMarkedList_iff hrep.valid hM kept x).mp h1
      exact hrep.valid.ordWithin.2.2 u x hu
    · obtain ⟨_, ⟨u, hu⟩, _, _, _⟩ := (mem_tourMarkedList_iff hrep.valid hM fresh x).mp h2'
      exact hrep.valid.ordWithin.2.2 u x hu
  have hargsSS : ∀ a ∈ [tourH, kept, fresh, kept, fresh, last, h2], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact htourW
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · rcases hlast_ok with rfl | ⟨hl, _⟩ <;> omega
    · omega
  obtain ⟨bdSS, hbdSS, oSS, stSS, cSS, txSS, hrunSS, hrepOutSS, hm0, hm1, hm2, hm4, hEL, _,
    hptr5, hoSS_eq, hoSS_le, hzeroSS, hpatchSS, hfrSS, hftSS, hcostSS⟩ :=
    outSmallSideMul_spec tourOutSpec w vCap eCap p bOut (tourOp bTour 8) (tourOp bTour 7)
      (tourOp bTour 11) (tourOp bTour 9) hpO hw T tourH kept fresh kept fresh last h2
      sOut tx2 st.mem st.pos ω hargsSS hkeptLt hfreshLt hndK hndF hml_lt
      ⟨rfl, hrep⟩ hfoot hh2_pos hlast_ok hzero (by omega)
  have hrepSS : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour sWall) txSS stSS.mem := hrepOutSS.2
  set side := if (tourMarkedList sWall kept).length ≤ (tourMarkedList sWall fresh).length then 0 else 1
  set Y := tourMarkedList sWall (if side = 0 then kept else fresh)
  have hoSS_eq' : oSS.value = stSS.mem (h2 + 3) + 1 + Y.length := hoSS_eq
  obtain ⟨hndY, hYE, hYkeep, hpotY⟩ :=
    tourMarkPot_split_step hrep.valid hM hkM hME₀ hK hkeptR hfreshNotR hR' hother hunion
  set r3 := Function.update r2 9 oSS.value
  have hcallSS : Runs w p ω
      (.call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26])
      { st with regs := r2 } .normal ⟨stSS.mem, r3, stSS.pos⟩
      (argsSize [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] + cSS + 1) :=
    runs_call_iff.mpr ⟨_, bdSS, oSS, stSS, cSS,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, r1, hr0])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, r1, hr24])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, r1, hr25])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, r1, hr24])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, r1, hr25])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r2, r1])) <|
      evalArgs_nil _ _,
      hbdSS, hrunSS, rfl, rfl, rfl⟩
  have hpreSS := outSplitPrefixAt_snoc (ptr := stSS.mem (h2 + 3)) (Y := Y)
    (avoid' := fun a => (tourAsmRep vCap eCap).foot tourH txSS a ∨ a < statePtr + 3)
    hpre hh2_pos (le_refl _) hptr5 hoSS_eq'.symm.le
    (fun a ha hna h2' => by
      rcases h2' with hf | hex
      · rcases hftSS a hf with h1 | ⟨hge, _⟩
        · exact hna (Or.inl h1)
        · omega
      · exact hna (Or.inr hex))
    (fun i hi h2' => by
      rcases h2' with hf | hex
      · rcases hftSS (h2 + i) hf with h1 | ⟨hge, _⟩
        · exact absurd (hfoot _ h1) (by omega)
        · omega
      · omega)
    (fun i hi h2' => by
      rcases h2' with hf | hex
      · rcases hftSS (stSS.mem (h2 + 3) + i) hf with h1 | ⟨_, hlt⟩
        · exact absurd (hfoot _ h1) (by omega)
        · omega
      · omega)
    (fun a ha hna hneL => hfrSS a ha (fun hf => hna (Or.inl hf)) hneL)
    hpatchSS hm0 hm1 hm2 (by change (if _ then 0 else 1) ≤ 1; split_ifs <;> omega) rfl hm4 hEL hndY hYE hYkeep
  have hstSS_keep : ∀ i < 3, stSS.mem (statePtr + i) = st.mem (statePtr + i) := fun i hi =>
    hfrSS (statePtr + i) (by omega) (hst_disj_foot i hi)
      (by rcases hst_disj_last with rfl | h1 | h2'
          · exact Or.inl rfl
          · exact Or.inr (by omega)
          · exact Or.inr (by omega))
  set splitPtr1 := if splitPtr = 0 then h2 else splitPtr
  set mA := if splitPtr = 0 then Function.update stSS.mem (statePtr + 1) h2 else stSS.mem
  set mB := Function.update mA (statePtr + 2) h2
  have hcond_sp : ∃ cSp,
      Runs w p ω
        (.cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
          (.store (.bin .add (.reg 7) (.const 1)) (.reg 26)) .nop)
        ⟨stSS.mem, r3, stSS.pos⟩ .normal ⟨mA, r3, stSS.pos⟩ cSp ∧ cSp ≤ 15 := by
    by_cases hsp0 : splitPtr = 0
    · have hev : (Expr.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0)).eval w
          ⟨stSS.mem, r3, stSS.pos⟩ = some 1 := by
        have hld : (Expr.load (.bin .add (.reg 7) (.const 1))).eval w ⟨stSS.mem, r3, stSS.pos⟩ = some 0 :=
          Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr7]))
              (Expr.eval_const (by omega)) (by omega))
            ((hstSS_keep 1 (by decide)).trans (hst_mem.2.1.trans hsp0))
        rw [Expr.eval, hld]
        simp [Expr.eval, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hst1 : Runs w p ω (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
          ⟨stSS.mem, r3, stSS.pos⟩ .normal ⟨mA, r3, stSS.pos⟩ 5 :=
        runs_store_iff.mpr ⟨statePtr + 1, h2,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr7]))
            (Expr.eval_const (by omega)) (by omega),
          Expr.eval_reg_of_eq (by simp [r3, r2, r1]), rfl, by simp [mA, hsp0], rfl⟩
      exact ⟨_, runs_cond_iff.mpr ⟨1, 5, hev, by simpa using hst1, rfl⟩, by simp [Expr.size]⟩
    · have hev : (Expr.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0)).eval w
          ⟨stSS.mem, r3, stSS.pos⟩ = some 0 := by
        have hld : (Expr.load (.bin .add (.reg 7) (.const 1))).eval w ⟨stSS.mem, r3, stSS.pos⟩ = some splitPtr :=
          Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr7]))
              (Expr.eval_const (by omega)) (by omega))
            ((hstSS_keep 1 (by decide)).trans hst_mem.2.1)
        rw [Expr.eval, hld]
        simp [Expr.eval, BinOp.eval, hsp0, (by omega : 0 < 2 ^ w)]
      have hnop : Runs w p ω .nop ⟨stSS.mem, r3, stSS.pos⟩ .normal ⟨mA, r3, stSS.pos⟩ 1 :=
        runs_nop_iff.mpr ⟨rfl, by simp [mA, hsp0], rfl⟩
      exact ⟨_, runs_cond_iff.mpr ⟨0, 1, hev, by simpa using hnop, rfl⟩, by simp [Expr.size]⟩
  obtain ⟨cSp, hrunSp, hcSp⟩ := hcond_sp
  have hstLast : Runs w p ω (.store (.bin .add (.reg 7) (.const 2)) (.reg 26))
      ⟨mA, r3, stSS.pos⟩ .normal ⟨mB, r3, stSS.pos⟩ 5 :=
    runs_store_iff.mpr ⟨statePtr + 2, h2,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr7]))
        (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq (by simp [r3, r2, r1]), rfl, rfl, rfl⟩
  have hmB_out : ∀ a, (a < statePtr ∨ statePtr + 3 ≤ a) → mB a = stSS.mem a := fun a ha => by
    simp only [mB, mA]
    rw [Function.update_of_ne (by omega)]
    split_ifs
    · rw [Function.update_of_ne (by omega)]
    · rfl
  have hfootSS_disj_st : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH txSS (statePtr + i) := fun i hi hf => by
    rcases hftSS (statePtr + i) hf with h0 | ⟨hge, _⟩
    · exact hst_disj_foot i hi h0
    · omega
  have hlocB := tourAsmRep_local vCap eCap tourH (tourToAsmTour sWall) txSS stSS.mem mB fun a ha => by
    refine (hmB_out a ?_).symm
    by_contra hnot; push Not at hnot
    exact hfootSS_disj_st (a - statePtr) (by omega) (by convert ha using 1; omega)
  have hspAt_mB : SplitEntriesAt mB spPtr L :=
    asmFirstSplitEntriesAt_congr hspAt fun a ha1 ha2 =>
      (hmB_out a (by omega)).trans (hfrSS a (by omega) (hsp_disj a ha1 ha2) (by omega))
  have hpreB := outSplitPrefixAt_mono hpreSS (le_refl _) (fun _ _ hna => hna)
    (fun a _ hna => hmB_out a (by by_contra hnot; push Not at hnot; exact hna (Or.inr (by omega))))
  have hfootSS_lt : ∀ a, (tourAsmRep vCap eCap).foot tourH txSS a → a < oSS.value := fun a ha => by
    rcases hftSS a ha with h0 | ⟨_, hlt⟩
    · exact lt_of_lt_of_le (hfoot a h0) (by omega)
    · omega
  have hsp_disjSS : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length →
      ¬ (tourAsmRep vCap eCap).foot tourH txSS a := fun a ha1 ha2 hf => by
    rcases hftSS a hf with h0 | ⟨hge, _⟩
    · exact hsp_disj a ha1 ha2 h0
    · omega
  obtain ⟨hEnd, stRel, cRel, txF, splitPtrF, lastF, YsRel, hrunRel, hrepF, hMF, hKF,
    hstF0, hstF1, hstF2, hlstF, hpreF, hpotRel, hhEndLo, hhEndHi, hzeroF, hfrRel, hftRel, hcostRel⟩ :=
    asmFirstTourConsumeRel_runs hpT hpO hw (s := sWall) (tx := txSS) (mem := mB) (pos := stSS.pos) (ω := ω)
      (hlocB.1 hrepSS) hfootSS_lt (fun a ha => (hmB_out a (Or.inr (by omega))).trans (hzeroSS a ha))
      hspAt_mB (by omega) hsp_disjSS
      ⟨by simp only [mB, mA]
          rw [Function.update_of_ne (by omega)]
          split_ifs
          · rw [Function.update_of_ne (by omega)]; exact (hstSS_keep 0 (by decide)).trans hst_mem.1
          · exact (hstSS_keep 0 (by decide)).trans hst_mem.1,
       by simp only [mB, mA, splitPtr1]
          rw [Function.update_of_ne (by omega)]
          split_ifs with h0
          · exact Function.update_self _ _ _
          · exact (hstSS_keep 1 (by decide)).trans hst_mem.2.1,
       by simp [mB]⟩
      (by omega) hfootSS_disj_st hst_disj_sp (Or.inr (Or.inr (by omega))) (Or.inr (Or.inr (by omega)))
      hspIdx_le hdrop hrest_stop hchain hM hkM hME₀ hK hpreB (by omega)
  set r4 := Function.update r3 9 hEnd
  have hcallRel : Runs w p ω (.call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
      ⟨mB, r3, stSS.pos⟩ .normal ⟨stRel.mem, r4, stRel.pos⟩
      (argsSize [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9] + cRel + 1) :=
    runs_call_iff.mpr ⟨_, _, .returned hEnd, stRel, cRel,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr0])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr5])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr10])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r3, r2, r1, hr7])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r3])) <|
      evalArgs_nil _ _,
      hpRel, hrunRel, rfl, rfl, rfl⟩
  have hrunAll := runs_seq_normal ha26 (runs_seq_normal ha27 (runs_seq_normal hcallSS
    (runs_seq_normal hrunSp (runs_seq_normal hstLast hcallRel))))
  refine ⟨hEnd, ⟨stRel.mem, r4, stRel.pos⟩, _, txF, splitPtrF, lastF, Y, YsRel, hrunAll,
    by simp [r4], fun r h9 h26 h27 => by simp [r4, r3, r2, r1, h9, h26, h27],
    hrepF, hMF, hKF, hstF0, hstF1, hstF2, by rcases hlstF with rfl | hge <;> omega,
    by simpa [List.append_assoc] using hpreF, ?_, by omega, by omega, hzeroF,
    fun a ha hnf hstO hnl => by
      have hnfSS : ¬ (tourAsmRep vCap eCap).foot tourH txSS a := fun hf => by
        rcases hftSS a hf with h0 | ⟨hge, _⟩
        · exact hnf h0
        · omega
      exact (hfrRel a (by omega) hnfSS hstO (Or.inr (by omega))).trans
        ((hmB_out a hstO).trans (hfrSS a ha hnf hnl)),
    fun a ha => by
      rcases hftRel a ha with h1 | ⟨hge, hlt⟩
      · rcases hftSS a h1 with h0 | ⟨hge0, hlt0⟩
        · exact Or.inl h0
        · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, hlt⟩, ?_⟩
  · simp only [MGraph.batchEnc, MGraph.updateEnc]
    have hpotY' : Y.length + tourMarkPot keep sWall ≤
        min ((S_cur.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))).deg kept)
            ((S_cur.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))).deg fresh) +
          tourMarkPot keep sPrev := hpotY
    clear * - hpotY' hpotRel; omega
  · rw [← hlocB.2] at hcostRel
    have hcostSS' : cSS + (tourAsmRep vCap eCap).phi tourH txSS stSS.mem ≤
        outSmallSideMul * (tourOutSpec.mul + 1) * (Y.length + 1) * ordStoreLog eCap +
          (tourAsmRep vCap eCap).phi tourH tx2 st.mem := hcostSS
    set y1 := Y.length; set y2 := (YsRel.map List.length).sum; set rLen := relL.length
    set S_tot := y1 + y2 + (1 + rLen) + 1
    have hss_le : outSmallSideMul * (tourOutSpec.mul + 1) * (y1 + 1) * ordStoreLog eCap ≤
        outSmallSideMul * (tourOutSpec.mul + 1) * S_tot * ordStoreLog eCap :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have hrel_le : tourConsumeRelMul * (y2 + rLen + 1) * ordStoreLog eCap ≤
        tourConsumeRelMul * S_tot * ordStoreLog eCap :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have hov : 80 ≤ 80 * S_tot * ordStoreLog eCap :=
      le_trans (by omega : 80 ≤ 80 * S_tot) (Nat.le_mul_of_pos_right _ htl)
    have hdist : (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) * S_tot *
          ordStoreLog eCap =
        outSmallSideMul * (tourOutSpec.mul + 1) * S_tot * ordStoreLog eCap +
        tourConsumeRelMul * S_tot * ordStoreLog eCap + 80 * S_tot * ordStoreLog eCap := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
    simp only [argsSize, Expr.size]
    clear * - hcostSS' hcostRel hcSp hss_le hrel_le hov hdist
    omega


end

end MinCostFlow.SparseCore.Program
