module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepTail

import Mathlib.Tactic

/-!
# Wall cases for `asmFirstTourBlockStepStmt` (`AssemblyFirstTourStepWalls`)

Verifies the two wall iterations of `asmFirstTourBlockStepStmt`:
1. `tourBlock_case_forestDel_runs`: wall forest `.delete e` (`isOpen = 0`), popping the split entry,
   running `tourOp 1` (`cut`), `tourOp 0` (`dropEdge e`), and `tourBlock_smallSide_and_rel_runs`.
2. `tourBlock_case_split_runs`: wall `.split v v' St Sh`, running `fApplyMove`, popping the split
   entry, reading `isRoot[v']`, running `tourOp 3` (`changeRoot`), and `tourBlock_smallSide_and_rel_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

private theorem walls_runs_seq_congr_right {w : ℕ} {p : Program} {ω : ℕ → Bool} {A B B' : Stmt}
    {s0 s1 : State} {c : ℕ}
    (h : Runs w p ω (A ;; B) s0 .normal s1 c)
    (hf : ∀ {sa sb cb}, Runs w p ω B sa .normal sb cb → Runs w p ω B' sa .normal sb cb) :
    Runs w p ω (A ;; B') s0 .normal s1 c := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hEq, _⟩ | ⟨sm, cA, cB, hA, hB, rfl⟩
  · cases hEq
  · exact runs_seq_normal hA (hf hB)

private theorem walls_runs_seq_r4 {w : ℕ} {p : Program} {ω : ℕ → Bool} {A B C D E : Stmt}
    {s0 s1 : State} {c : ℕ} (h : Runs w p ω ((A ;; B ;; C ;; D) ;; E) s0 .normal s1 c) :
    Runs w p ω (A ;; B ;; C ;; D ;; E) s0 .normal s1 c :=
  walls_runs_seq_congr_right (runs_seq_assoc h) fun h1 =>
    walls_runs_seq_congr_right (runs_seq_assoc h1) fun h2 => runs_seq_assoc h2

private theorem walls_runs_seq_r5 {w : ℕ} {p : Program} {ω : ℕ → Bool} {A B C D E F : Stmt}
    {s0 s1 : State} {c : ℕ} (h : Runs w p ω ((A ;; B ;; C ;; D ;; E) ;; F) s0 .normal s1 c) :
    Runs w p ω (A ;; B ;; C ;; D ;; E ;; F) s0 .normal s1 c :=
  walls_runs_seq_congr_right (runs_seq_assoc h) walls_runs_seq_r4

public section

/-! ## 2. Wall Case 3: forest `.delete e` (`isOpen = 0`) -/

/-- Case 3 (wall forest `.delete e`, `isOpen = 0`): pops wall split entry, calls `tourOp 1` (`cut`),
`tourOp 0` (`dropEdge e`), `outIdxSmallSide`, and `fConsumeRel`. -/
theorem tourBlock_case_forestDel_runs
    {w vCap eCap bSelf bTour bOut tourH spPtr statePtr hCur spIdx splitPtr last e kept fresh : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpRel : p.procs[bSelf + 0]? = some (asmFirstTourConsumeRelStmt (tourOp bTour 1) (outIdxSmallSide bOut)))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {s s_f : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {st : State}
    {L relL spRest : List CompSplitEntry}
    {keep M E₀ St Sh : Finset ℕ} {G₀ S_cur S_f : MGraph}
    {P_done P_rel : List Update} {Ys_done : List (List End)}
    (hr0 : st.regs 0 = tourH) (hr5 : st.regs 5 = spPtr) (hr7 : st.regs 7 = statePtr)
    (hr9 : st.regs 9 = hCur) (hr10 : st.regs 10 = L.length) (hr17 : st.regs 17 = e)
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx st.mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < hCur)
    (hzero : ZeroFrom st.mem hCur)
    (hspAt : SplitEntriesAt st.mem spPtr L) (hsp_le : spPtr + 1 + 4 * L.length ≤ hCur)
    (hsp_disj : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → ¬ (tourAsmRep vCap eCap).foot tourH tx a)
    (hst_mem : st.mem statePtr = spIdx ∧ st.mem (statePtr + 1) = splitPtr ∧ st.mem (statePtr + 2) = last)
    (hst_le : statePtr + 3 ≤ hCur)
    (hst_disj_foot : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx (statePtr + i))
    (hst_disj_sp : statePtr + 3 ≤ spPtr ∨ spPtr + 1 + 4 * L.length ≤ statePtr)
    (hst_disj_last : last = 0 ∨ last + 4 < statePtr ∨ statePtr + 3 ≤ last + 4)
    (hsp_disj_last : last = 0 ∨ last + 4 < spPtr ∨ spPtr + 1 + 4 * L.length ≤ last + 4)
    (hspIdx_lt : spIdx < L.length)
    (hdrop : L.drop spIdx = ⟨false, 0, kept, fresh⟩ :: relL ++ spRest)
    (hrest_stop : ∀ d rest, spRest = d :: rest → d.isRelease = false)
    (he : e ∈ s.rf.F.E) (heLt : e < eCap) (heM : e ∉ M) (hek : e ∉ keep)
    (hkept_eq : kept = s.rf.root (s.rf.F.tail e))
    (hfreshLt : fresh < vCap) (hfreshV : fresh ∈ s.rf.F.V) (hfreshNotR : fresh ∉ s.rf.R)
    (huniq' : ∀ v ∈ s.rf.F.V,
      ∃! r, r ∈ insert fresh s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r)
    (hSt : ∀ f ∈ keep, f ∈ St ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, true)) = fresh)
    (hSh : ∀ f ∈ keep, f ∈ Sh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, false)) = fresh)
    (hM : TourMarksAt s M) (hkM : keep ⊆ M) (hME₀ : M ⊆ E₀) (hK : TourKeepMatch keep s S_cur)
    (hpre : OutSplitPrefixAt st.mem splitPtr last hCur
      (fun a => (tourAsmRep vCap eCap).foot tourH tx a ∨ a < statePtr + 3)
      keep E₀ G₀ P_done S_cur Ys_done)
    (hchain : TourRelChain vCap eCap keep M (tourApplyEdit (tourCut s e fresh) (.dropEdge e))
      (S_cur.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))) relL P_rel s_f S_f)
    (hroom : hCur + 51 + (1 + relL.length) * tourSplitStepSpace eCap + 2 < 2 ^ w) :
    ∃ hEnd stF c txF splitPtrF lastF Y YsRel,
      Runs w p ω
        (.assign 22 (.load (.reg 7)) ;;
         .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 4) (.reg 22))) ;;
         .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
         .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
         .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
         .call 9 (tourOp bTour 1) [.reg 0, .reg 17, .reg 25, .reg 9] ;;
         .store (.reg 9) (.const 1) ;;
         .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
         .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
         .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)] ;;
         .assign 26 (.reg 9) ;;
         .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
         .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
         .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
           (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
           .nop ;;
         .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
         .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
        st .normal stF c ∧
      stF.regs 9 = hEnd ∧
      (∀ r, r ≠ 9 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → stF.regs r = st.regs r) ∧
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s_f) txF stF.mem ∧
      TourMarksAt s_f M ∧ TourKeepMatch keep s_f S_f ∧
      stF.mem statePtr = spIdx + 1 + relL.length ∧
      stF.mem (statePtr + 1) = splitPtrF ∧ stF.mem (statePtr + 2) = lastF ∧ hCur ≤ lastF ∧
      OutSplitPrefixAt stF.mem splitPtrF lastF hEnd
        (fun a => (tourAsmRep vCap eCap).foot tourH txF a ∨ a < statePtr + 3)
        keep E₀ G₀ (P_done ++ .split kept fresh (St ∩ keep) (Sh ∩ keep) :: P_rel) S_f
        (Ys_done ++ Y :: YsRel) ∧
      Y.length + (YsRel.map List.length).sum + tourMarkPot keep s_f ≤
        S_cur.batchEnc (.split kept fresh (St ∩ keep) (Sh ∩ keep) :: P_rel) +
          tourMarkPot keep s ∧
      hCur + 5 ≤ hEnd ∧
      hEnd ≤ hCur + 51 + (1 + relL.length) * tourSplitStepSpace eCap ∧
      ZeroFrom stF.mem hEnd ∧
      (∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a →
        (a < statePtr ∨ statePtr + 3 ≤ a) → (last = 0 ∨ a ≠ last + 4) → stF.mem a = st.mem a) ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH txF a →
        (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < hEnd)) ∧
      c + (tourAsmRep vCap eCap).phi tourH txF stF.mem ≤
        tourBlockCaseMul * (Y.length + (YsRel.map List.length).sum + (1 + relL.length) + 4) *
          ordStoreLog eCap + (tourAsmRep vCap eCap).phi tourH tx st.mem := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx st.mem at hrep
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hord_le : ordHandleOf tourH vCap eCap ≤ hCur := hrep.fixed_le_heap hfoot
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by omega : hCur + 1 < 2 ^ w)).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by omega)
  have hdrop0 : L[spIdx]'hspIdx_lt = ⟨false, 0, kept, fresh⟩ := by
    have := List.drop_eq_getElem_cons hspIdx_lt; rw [hdrop] at this; exact (List.cons.inj this.symm).1
  have hdrop1 : L.drop (spIdx + 1) = relL ++ spRest := by
    have := List.drop_eq_getElem_cons hspIdx_lt; rw [hdrop] at this; exact (List.cons.inj this.symm).2
  obtain ⟨st1, c1, hrun1, hst1_mem, hr24_1, hr25_1, hregs1, hc1⟩ :=
    tourBlock_popSplitEntry_runs (p := p) (ω := ω) hwide (by omega) (by omega) hr5 hr7 hspAt hspIdx_lt hst_mem.1
  rw [hdrop0] at hr24_1 hr25_1
  have hm1_out : ∀ a, a ≠ statePtr → st1.mem a = st.mem a := fun a ha => by
    rw [hst1_mem]; exact Function.update_of_ne ha _ _
  have hloc1 := tourAsmRep_local vCap eCap tourH (tourToAsmTour s) tx st.mem st1.mem fun a ha =>
    (hm1_out a (fun hEq => hst_disj_foot 0 (by decide) (by simpa [hEq] using ha))).symm
  have hsync := tourStep_wall_forestDelete_sync hrep.valid heLt hM hK he heM hek hkept_eq
    hfreshV hfreshNotR huniq' hSt hSh
  obtain ⟨hevDrop, _, hM2, hK2, hkeptR, hother2, hunion2⟩ := hsync
  have hkeptLt : kept < vCap := hrep.valid.verts_lt kept (hrep.valid.roots_sub hkeptR)
  have hImpl := (tourDS_implements w vCap eCap p bTour hpT hw).2
  have hargs1 : ∀ a ∈ [tourH, e, fresh, hCur], a < 2 ^ w := by
    intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl
    · exact htourW
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · omega
  have hpre1 : (tourContract vCap eCap tourMul tourAlloc).pre 1 s [tourH, e, fresh, hCur] st1.mem :=
    ⟨tourH, e, fresh, hCur, rfl, he, hfreshLt, hfreshV, hfreshNotR, huniq'⟩
  have hsp1 : hCur + (tourContract vCap eCap tourMul tourAlloc).space 1 s [tourH, e, fresh, hCur] st1.mem < 2 ^ w := by
    simp only [tourContract]; unfold tourSplitStepSpace at hroom; omega
  have hzero1 : ZeroFrom st1.mem (heapArg [tourH, e, fresh, hCur]) := fun a ha => by
    change hCur ≤ a at ha; exact (hm1_out a (by omega)).trans (hzero a ha)
  obtain ⟨bdCut, hbdCut, oCut, stCut, cCut, hrunCut, s1, tx1, hrep1, hpostCut, hrespCut, hcostCut⟩ :=
    hImpl.2.2 1 tourH s tx [tourH, e, fresh, hCur] st1.mem st1.pos ω hargs1 rfl
      (hloc1.1 hrep) hpre1 hfoot hzero1 hsp1
  have hs1_eq : s1 = tourCut s e fresh := by simpa [tourContract] using hpostCut
  subst hs1_eq
  have hhaCut : heapArg [tourH, e, fresh, hCur] = hCur := rfl
  rw [hhaCut] at hrespCut
  simp only [tourContract] at hrespCut hcostCut
  have hoCut_lo : hCur ≤ oCut.value := hrespCut.1
  have hoCut_hi : oCut.value ≤ hCur + 2 := hrespCut.2.1
  set r2 := Function.update st1.regs 9 oCut.value
  have hcallCut : Runs w p ω (.call 9 (tourOp bTour 1) [.reg 0, .reg 17, .reg 25, .reg 9])
      st1 .normal ⟨stCut.mem, r2, stCut.pos⟩
      (argsSize [.reg 0, .reg 17, .reg 25, .reg 9] + cCut + 1) :=
    runs_call_iff.mpr ⟨_, bdCut, oCut, stCut, cCut,
      evalArgs_cons (Expr.eval_reg_of_eq ((hregs1 0 (by decide) (by decide) (by decide) (by decide)).trans hr0)) <|
      evalArgs_cons (Expr.eval_reg_of_eq ((hregs1 17 (by decide) (by decide) (by decide) (by decide)).trans hr17)) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr25_1) <|
      evalArgs_cons (Expr.eval_reg_of_eq ((hregs1 9 (by decide) (by decide) (by decide) (by decide)).trans hr9)) <|
      evalArgs_nil _ _,
      hbdCut, hrunCut, rfl, rfl, rfl⟩
  have hfoot1 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx1 a → a < oCut.value := fun a ha => by
    rcases hrespCut.2.2.2.2 a ha with h0 | ⟨_, h2⟩
    · exact lt_of_lt_of_le (hfoot a h0) hoCut_lo
    · exact h2
  have hrep1' : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour (tourCut s e fresh)) tx1 stCut.mem := hrep1
  obtain ⟨h2, st2, cDrop, tx2, hrunDrop, hr9_2, hregs2, hrep2, hh2Lo, hh2Hi, hzero2, hfr2, hft2, hcost2⟩ :=
    tourBlock_case_nonForestDel_runs (ω := ω) hpT hw (st := ⟨stCut.mem, r2, stCut.pos⟩)
      (by simp [r2, hregs1 0 (by decide) (by decide) (by decide) (by decide), hr0])
      (by simp [r2])
      (by simp [r2, hregs1 17 (by decide) (by decide) (by decide) (by decide), hr17])
      hrep1' hfoot1 hrespCut.2.2.1 hevDrop
      (by unfold tourSplitStepSpace at hroom; omega)
  have hft12 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a →
      (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < h2) := fun a ha => by
    rcases hft2 a ha with h1 | ⟨hge, hlt⟩
    · rcases hrespCut.2.2.2.2 a h1 with h0 | ⟨hge0, hlt0⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hge0, by omega⟩
    · exact Or.inr ⟨by omega, hlt⟩
  have hfr12 : ∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a → a ≠ statePtr →
      st2.mem a = st.mem a := fun a ha hnf hneS => by
    have hnf1 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 a := fun hf1 => by
      rcases hrespCut.2.2.2.2 a hf1 with h0 | ⟨hge, _⟩
      · exact hnf h0
      · omega
    exact (hfr2 a (by omega) hnf1).trans ((hrespCut.2.2.2.1 a ha hnf).trans (hm1_out a hneS))
  have hfoot2 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a → a < h2 := fun a ha => by
    rcases hft12 a ha with h0 | ⟨_, hlt⟩
    · exact lt_of_lt_of_le (hfoot a h0) (by omega)
    · exact hlt
  have hst2_disj_foot : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx2 (statePtr + i) := fun i hi hf => by
    rcases hft12 (statePtr + i) hf with h0 | ⟨hge, _⟩
    · exact hst_disj_foot i hi h0
    · omega
  have hsp2_disj : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length →
      ¬ (tourAsmRep vCap eCap).foot tourH tx2 a := fun a ha1 ha2 hf => by
    rcases hft12 a hf with h0 | ⟨hge, _⟩
    · exact hsp_disj a ha1 ha2 h0
    · omega
  have hspAt2 : SplitEntriesAt st2.mem spPtr L :=
    asmFirstSplitEntriesAt_congr hspAt fun a ha1 ha2 =>
      hfr12 a (by omega) (hsp_disj a ha1 ha2) (by omega)
  have hst2_mem : st2.mem statePtr = spIdx + 1 ∧ st2.mem (statePtr + 1) = splitPtr ∧
      st2.mem (statePtr + 2) = last := by
    have hnfS : ¬ (tourAsmRep vCap eCap).foot tourH tx statePtr := by
      have := hst_disj_foot 0 (by decide); rwa [Nat.add_zero] at this
    have hnf0 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 statePtr := fun hf1 => by
      rcases hrespCut.2.2.2.2 statePtr hf1 with h0 | ⟨hge, _⟩
      · exact hnfS h0
      · omega
    refine ⟨(hfr2 statePtr (by omega) hnf0).trans
        ((hrespCut.2.2.2.1 statePtr (by omega) hnfS).trans
          (by rw [hst1_mem, Function.update_self])),
      (hfr12 (statePtr + 1) (by omega) (hst_disj_foot 1 (by decide)) (by omega)).trans hst_mem.2.1,
      (hfr12 (statePtr + 2) (by omega) (hst_disj_foot 2 (by decide)) (by omega)).trans hst_mem.2.2⟩
  have hpre2 := outSplitPrefixAt_mono
    (avoid' := fun a => (tourAsmRep vCap eCap).foot tourH tx2 a ∨ a < statePtr + 3)
    hpre (by omega : hCur ≤ h2)
    (fun a ha hna h2' => by
      rcases h2' with hf | hex
      · rcases hft12 a hf with h0 | ⟨hge, _⟩
        · exact hna (Or.inl h0)
        · omega
      · exact hna (Or.inr hex))
    (fun a ha hna => hfr12 a ha (fun hf => hna (Or.inl hf))
      (fun hEq => hna (Or.inr (by omega))))
  have hroomTail : h2 + outSmallSideSpace tourOutSpec (2 * eCap) +
      relL.length * tourSplitStepSpace eCap + 2 < 2 ^ w := by
    have : (1 + relL.length) * tourSplitStepSpace eCap =
        2 + outSmallSideSpace tourOutSpec (2 * eCap) + relL.length * tourSplitStepSpace eCap := by
      rw [Nat.add_mul, Nat.one_mul]; unfold tourSplitStepSpace; omega
    omega
  obtain ⟨hEnd, stF, cTail, txF, splitPtrF, lastF, Y, YsRel, hrunTail, hr9F, hregsF,
    hrepF, hMF, hKF, hstF0, hstF1, hstF2, hlstF, hpreF, hpotF, hhEndLo, hhEndHi, hzeroF, hfrTail, hftTail, hcostTail⟩ :=
    tourBlock_smallSide_and_rel_runs hpT hpO hpRel hw
      (sPrev := s) (sWall := tourApplyEdit (tourCut s e fresh) (.dropEdge e))
      (tx2 := tx2) (st := st2) (spIdx := spIdx) (splitPtr := splitPtr) (last := last)
      (by rw [hregs2 0 (by decide)]; simp [r2, hregs1 0 (by decide) (by decide) (by decide) (by decide), hr0])
      (by rw [hregs2 5 (by decide)]; simp [r2, hregs1 5 (by decide) (by decide) (by decide) (by decide), hr5])
      (by rw [hregs2 7 (by decide)]; simp [r2, hregs1 7 (by decide) (by decide) (by decide) (by decide), hr7])
      hr9_2
      (by rw [hregs2 10 (by decide)]; simp [r2, hregs1 10 (by decide) (by decide) (by decide) (by decide), hr10])
      (by rw [hregs2 24 (by decide)]; simp [r2, hr24_1])
      (by rw [hregs2 25 (by decide)]; simp [r2, hr25_1])
      hrep2 hfoot2 hzero2 hspAt2 (by omega) hsp2_disj hst2_mem (by omega) hst2_disj_foot
      hst_disj_sp hst_disj_last hsp_disj_last hspIdx_lt hdrop1 hrest_stop
      hkeptLt hfreshLt hkeptR hfreshNotR rfl hother2 hunion2 hM2 hkM hME₀ hK2 hpre2 hchain hroomTail
  have hrunFlat :=
    walls_runs_seq_r5 (runs_seq_normal hrun1 (runs_seq_normal hcallCut
      (walls_runs_seq_r4 (runs_seq_normal hrunDrop hrunTail))))
  have hspTot : hEnd ≤ hCur + 51 + (1 + relL.length) * tourSplitStepSpace eCap := by
    have : (1 + relL.length) * tourSplitStepSpace eCap =
        2 + outSmallSideSpace tourOutSpec (2 * eCap) + relL.length * tourSplitStepSpace eCap := by
      rw [Nat.add_mul, Nat.one_mul]; unfold tourSplitStepSpace; omega
    omega
  refine ⟨hEnd, stF, _, txF, splitPtrF, lastF, Y, YsRel, hrunFlat, hr9F,
    fun r h9 h22 h23 h24 h25 h26 h27 =>
      (hregsF r h9 h26 h27).trans ((hregs2 r h9).trans
        (by simp [r2, h9, hregs1 r h22 h23 h24 h25])),
    hrepF, hMF, hKF, hstF0, hstF1, hstF2, by omega, hpreF, hpotF, by omega, hspTot, hzeroF,
    fun a ha hnf hstO hnl =>
      (hfrTail a (by omega) (fun hf => by
        rcases hft12 a hf with h0 | ⟨hge, _⟩
        · exact hnf h0
        · omega) hstO hnl).trans (hfr12 a ha hnf (by omega)),
    fun a ha => by
      rcases hftTail a ha with h1 | ⟨hge, hlt⟩
      · rcases hft12 a h1 with h0 | ⟨hge0, hlt0⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hge0, by omega⟩
      · exact Or.inr ⟨by omega, hlt⟩, ?_⟩
  have hphi1 : (tourDSRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx st1.mem := hloc1.2
  have hphi_cut : (tourAsmRep vCap eCap).phi tourH tx1 stCut.mem = (tourDSRep vCap eCap).phi tourH tx1 stCut.mem ∧
      (tourAsmRep vCap eCap).phi tourH tx st.mem = (tourDSRep vCap eCap).phi tourH tx st.mem := ⟨rfl, rfl⟩
  rw [← hphi1, ← ordStoreLog_eq_tourLog] at hcostCut
  rw [hphi_cut.1] at hcost2
  rw [hphi_cut.2]
  set S_tot := Y.length + (YsRel.map List.length).sum + (1 + relL.length) + 4
  have ht5 : tourMul * ordStoreLog eCap + (4 * tourMul + 40) * ordStoreLog eCap ≤
      (5 * tourMul + 40) * S_tot * ordStoreLog eCap := by
    have h1 : tourMul + (4 * tourMul + 40) = 5 * tourMul + 40 := by omega
    rw [← Nat.add_mul, h1]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have htail_le : (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) *
      (Y.length + (YsRel.map List.length).sum + (1 + relL.length) + 1) * ordStoreLog eCap ≤
      (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) * S_tot * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hov : 120 ≤ 380 * S_tot * ordStoreLog eCap :=
    le_trans (by omega : 120 ≤ 380 * S_tot) (Nat.le_mul_of_pos_right _ htl)
  have hbm : (5 * tourMul + 40) * S_tot * ordStoreLog eCap +
      (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) * S_tot * ordStoreLog eCap +
      380 * S_tot * ordStoreLog eCap ≤
      tourBlockCaseMul * S_tot * ordStoreLog eCap := by
    rw [tourBlockCaseMul_eq, tourBlockCaseMulFn_eq]
    rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  simp only [argsSize, Expr.size]
  clear * - hc1 hcostCut hcost2 hcostTail ht5 htail_le hov hbm
  omega

/-! ## 3. Wall Case 4: vertex `.split v v' St Sh` -/

/-- Case 4 (wall `.split v v' St Sh`): calls `fApplyMove`, pops the split entry, reads `isRoot[v']`
to pick `rTmp`, calls `tourOp 3` (`changeRoot rTmp fresh`), `outIdxSmallSide`, and `fConsumeRel`. -/
theorem tourBlock_case_split_runs
    {w vCap eCap bSelf bTour bOut tourH spPtr statePtr ePtr hCur spIdx splitPtr last
      v v' m kept fresh : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpRel : p.procs[bSelf + 0]? = some (asmFirstTourConsumeRelStmt (tourOp bTour 1) (outIdxSmallSide bOut)))
    (hpMove : p.procs[bSelf + 1]? = some (asmFirstTourApplyMoveStmt (bTour + 75) (tourOp bTour 0)))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {sel : Finset End} {cMove : Bool} {s s_f : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {st : State}
    {L relL spRest : List CompSplitEntry}
    {keep M E₀ St Sh : Finset ℕ} {G₀ S_cur S_f : MGraph}
    {P_done P_rel : List Update} {Ys_done : List (List End)}
    (hr0 : st.regs 0 = tourH) (hr5 : st.regs 5 = spPtr) (hr7 : st.regs 7 = statePtr)
    (hr9 : st.regs 9 = hCur) (hr10 : st.regs 10 = L.length) (hr13 : st.regs 13 = ePtr)
    (hr17 : st.regs 17 = v) (hr18 : st.regs 18 = v')
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx st.mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < hCur)
    (hzero : ZeroFrom st.mem hCur)
    (hePtr_ge : ordHandleOf tourH vCap eCap ≤ ePtr) (hePtr_le : ePtr + 4 + m ≤ hCur)
    (htag : st.mem ePtr = 1 ∨ st.mem ePtr = 2)
    (hdec : decodeOrdEdit st.mem ePtr = (.moveEnds v v' sel cMove, 4 + m))
    (hEdit : TourEditValid vCap eCap s (.moveEnds v v' sel cMove))
    (hvalid1 : TourValid vCap eCap (tourApplyEdit s (.moveEnds v v' sel cMove)))
    (hspAt : SplitEntriesAt st.mem spPtr L) (hsp_le : spPtr + 1 + 4 * L.length ≤ hCur)
    (hsp_disj : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → ¬ (tourAsmRep vCap eCap).foot tourH tx a)
    (hst_mem : st.mem statePtr = spIdx ∧ st.mem (statePtr + 1) = splitPtr ∧ st.mem (statePtr + 2) = last)
    (hst_le : statePtr + 3 ≤ hCur)
    (hst_disj_foot : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx (statePtr + i))
    (hst_disj_sp : statePtr + 3 ≤ spPtr ∨ spPtr + 1 + 4 * L.length ≤ statePtr)
    (hst_disj_last : last = 0 ∨ last + 4 < statePtr ∨ statePtr + 3 ≤ last + 4)
    (hsp_disj_last : last = 0 ∨ last + 4 < spPtr ∨ spPtr + 1 + 4 * L.length ≤ last + 4)
    (hspIdx_lt : spIdx < L.length)
    (hdrop : L.drop spIdx = ⟨false, 0, kept, fresh⟩ :: relL ++ spRest)
    (hrest_stop : ∀ d rest, spRest = d :: rest → d.isRelease = false)
    (hkept_eq : kept = s.rf.root v)
    (hfreshLt : fresh < vCap)
    (hfreshV : fresh ∈ (tourApplyEdit s (.moveEnds v v' sel cMove)).rf.F.V)
    (hfreshNotR : fresh ∉ s.rf.R)
    (huniq' : ∀ w' ∈ (tourApplyEdit s (.moveEnds v v' sel cMove)).rf.F.V,
      ∃! r, r ∈ insert fresh s.rf.R ∧
        (tourApplyEdit s (.moveEnds v v' sel cMove)).rf.F.Connected w' r)
    (hSt : ∀ f ∈ keep, f ∈ St ↔
      (tourChangeRoot (tourApplyEdit s (.moveEnds v v' sel cMove))
        (if v' ∈ (tourApplyEdit s (.moveEnds v v' sel cMove)).rf.R then v' else v) fresh).rf.root
        (ordSrc (tourApplyEdit s (.moveEnds v v' sel cMove)).ord (f, true)) = fresh)
    (hSh : ∀ f ∈ keep, f ∈ Sh ↔
      (tourChangeRoot (tourApplyEdit s (.moveEnds v v' sel cMove))
        (if v' ∈ (tourApplyEdit s (.moveEnds v v' sel cMove)).rf.R then v' else v) fresh).rf.root
        (ordSrc (tourApplyEdit s (.moveEnds v v' sel cMove)).ord (f, false)) = fresh)
    (hM : TourMarksAt s M) (hkM : keep ⊆ M) (hME₀ : M ⊆ E₀) (hK : TourKeepMatch keep s S_cur)
    (hpre : OutSplitPrefixAt st.mem splitPtr last hCur
      (fun a => (tourAsmRep vCap eCap).foot tourH tx a ∨ a < statePtr + 3)
      keep E₀ G₀ P_done S_cur Ys_done)
    (hchain : TourRelChain vCap eCap keep M
      (tourChangeRoot (tourApplyEdit s (.moveEnds v v' sel cMove))
        (if v' ∈ (tourApplyEdit s (.moveEnds v v' sel cMove)).rf.R then v' else v) fresh)
      (S_cur.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))) relL P_rel s_f S_f)
    (hroom : hCur + (13 * m + 77) + (1 + relL.length) * tourSplitStepSpace eCap + 2 < 2 ^ w) :
    ∃ hEnd stF c txF splitPtrF lastF Y YsRel,
      Runs w p ω
        (.call 9 (bSelf + 1) [.reg 0, .reg 13, .reg 9] ;;
         .assign 22 (.load (.reg 7)) ;;
         .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 4) (.reg 22))) ;;
         .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
         .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
         .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
         .assign 26 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
         .assign 27 (.load (.bin .add (.reg 26) (.reg 18))) ;;
         .assign 28 (.reg 17) ;;
         .cond (.bin .eq (.reg 27) (.const 1)) (.assign 28 (.reg 18)) .nop ;;
         .call 9 (tourOp bTour 3) [.reg 0, .reg 28, .reg 25, .reg 9] ;;
         .assign 26 (.reg 9) ;;
         .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
         .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
         .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
           (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
           .nop ;;
         .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
         .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
        st .normal stF c ∧
      stF.regs 9 = hEnd ∧
      (∀ r, r ≠ 9 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → stF.regs r = st.regs r) ∧
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s_f) txF stF.mem ∧
      TourMarksAt s_f M ∧ TourKeepMatch keep s_f S_f ∧
      stF.mem statePtr = spIdx + 1 + relL.length ∧
      stF.mem (statePtr + 1) = splitPtrF ∧ stF.mem (statePtr + 2) = lastF ∧ hCur ≤ lastF ∧
      OutSplitPrefixAt stF.mem splitPtrF lastF hEnd
        (fun a => (tourAsmRep vCap eCap).foot tourH txF a ∨ a < statePtr + 3)
        keep E₀ G₀ (P_done ++ .split kept fresh (St ∩ keep) (Sh ∩ keep) :: P_rel) S_f
        (Ys_done ++ Y :: YsRel) ∧
      Y.length + (YsRel.map List.length).sum + tourMarkPot keep s_f ≤
        S_cur.batchEnc (.split kept fresh (St ∩ keep) (Sh ∩ keep) :: P_rel) +
          tourMarkPot keep s ∧
      hCur + 5 ≤ hEnd ∧
      hEnd ≤ hCur + (13 * m + 77) + (1 + relL.length) * tourSplitStepSpace eCap ∧
      ZeroFrom stF.mem hEnd ∧
      (∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a →
        (a < statePtr ∨ statePtr + 3 ≤ a) → (last = 0 ∨ a ≠ last + 4) → stF.mem a = st.mem a) ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH txF a →
        (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < hEnd)) ∧
      c + (tourAsmRep vCap eCap).phi tourH txF stF.mem ≤
        tourBlockCaseMul * (Y.length + (YsRel.map List.length).sum + (1 + relL.length) + (4 + m) + 5) *
          ordStoreLog eCap + (tourAsmRep vCap eCap).phi tourH tx st.mem := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx st.mem at hrep
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hord_le : ordHandleOf tourH vCap eCap ≤ hCur := hrep.fixed_le_heap hfoot
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by omega : hCur + 1 < 2 ^ w)).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by omega)
  have hdrop0 : L[spIdx]'hspIdx_lt = ⟨false, 0, kept, fresh⟩ := by
    have := List.drop_eq_getElem_cons hspIdx_lt; rw [hdrop] at this; exact (List.cons.inj this.symm).1
  have hdrop1 : L.drop (spIdx + 1) = relL ++ spRest := by
    have := List.drop_eq_getElem_cons hspIdx_lt; rw [hdrop] at this; exact (List.cons.inj this.symm).2
  set s1 := tourApplyEdit s (.moveEnds v v' sel cMove)
  set rTmp := if v' ∈ s1.rf.R then v' else v
  set sWall := tourChangeRoot s1 rTmp fresh
  obtain ⟨hrTmpR, _, hconn, hR'_eq, _, hM2, hK2, hkeptR, hother2, hunion2⟩ :=
    tourMove_changeRoot_sync hrep.valid hvalid1 hEdit hM hK hkept_eq hfreshLt hfreshV
      hfreshNotR huniq' hSt hSh
  have hkeptLt : kept < vCap := hrep.valid.verts_lt kept (hrep.valid.roots_sub hkeptR)
  -- Step 1: call `fApplyMove`
  obtain ⟨oM, stM, cM, tx1, hrunM, hrep1, hoMLo, hoMHi, hzero1, hfr1, hft1, hcostM⟩ :=
    asmFirstTourApplyMove_runs hpT hw (s := tourToAsmTour s) (tx := tx) (mem := st.mem) (pos := st.pos) (ω := ω)
      hrep hfoot hzero hePtr_ge hePtr_le htag hdec hEdit (by omega)
  set r1 := Function.update st.regs 9 oM.value
  have hcallM : Runs w p ω (.call 9 (bSelf + 1) [.reg 0, .reg 13, .reg 9])
      st .normal ⟨stM.mem, r1, stM.pos⟩ (argsSize [.reg 0, .reg 13, .reg 9] + cM + 1) :=
    runs_call_iff.mpr ⟨_, _, oM, stM, cM,
      evalArgs_cons (Expr.eval_reg_of_eq hr0) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr13) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr9) <|
      evalArgs_nil _ _,
      hpMove, hrunM, rfl, rfl, rfl⟩
  have hfoot1 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx1 a → a < oM.value := fun a ha => by
    rcases hft1 a ha with h0 | ⟨_, hlt⟩
    · exact lt_of_lt_of_le (hfoot a h0) hoMLo
    · exact hlt
  have hspAt1 : SplitEntriesAt stM.mem spPtr L :=
    asmFirstSplitEntriesAt_congr hspAt fun a ha1 ha2 => hfr1 a (by omega) (hsp_disj a ha1 ha2)
  have hst1_mem0 : stM.mem statePtr = spIdx :=
    (hfr1 statePtr (by omega) (by simpa using hst_disj_foot 0 (by decide))).trans hst_mem.1
  -- Step 2: pop split entry `(kept, fresh)` and increment `mem[statePtr]`
  obtain ⟨st2, cPop, hrunPop, hst2_mem, hr24_2, hr25_2, hregs2, hcPop⟩ :=
    tourBlock_popSplitEntry_runs (p := p) (ω := ω) (st := ⟨stM.mem, r1, stM.pos⟩)
      hwide (by omega) (by omega) (by simp [r1, hr5]) (by simp [r1, hr7]) hspAt1 hspIdx_lt hst1_mem0
  rw [hdrop0] at hr24_2 hr25_2
  have hm2_out : ∀ a, a ≠ statePtr → st2.mem a = stM.mem a := fun a ha => by
    rw [hst2_mem]; exact Function.update_of_ne ha _ _
  have hst1_disj_foot : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx1 (statePtr + i) := fun i hi hf => by
    rcases hft1 (statePtr + i) hf with h0 | ⟨hge, _⟩
    · exact hst_disj_foot i hi h0
    · omega
  have hloc2 := tourAsmRep_local vCap eCap tourH (tourToAsmTour s1) tx1 stM.mem st2.mem fun a ha =>
    (hm2_out a (fun hEq => hst1_disj_foot 0 (by decide) (by simpa [hEq] using ha))).symm
  have hrep1_m2 : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s1) tx1 st2.mem := hloc2.1 hrep1
  -- Step 3: read `isRoot[v']` and set `r28 := rTmp`
  have hv'Lt : v' < vCap := hEdit.2.1
  obtain ⟨hisRootBase, hisRootVal⟩ := tourAsmRep_isRoot_read hrep1_m2 hv'Lt
  set irBase := isRootBase tourH vCap
  set irVal := if v' ∈ s1.rf.R then 1 else 0
  set r3 := Function.update st2.regs 26 irBase
  set r4 := Function.update r3 27 irVal
  set r5 := Function.update r4 28 v
  set r6 := Function.update r5 28 rTmp
  have ha26 : Runs w p ω (.assign 26 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))))
      st2 .normal { st2 with regs := r3 } 5 :=
    runs_assign_iff.mpr ⟨irBase, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq ((hregs2 0 (by decide) (by decide) (by decide) (by decide)).trans
          (by simp [r1, hr0])))
        (Expr.eval_const (by simp [HDR_IS_ROOT]; omega))
        (by simp [HDR_IS_ROOT, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
      hisRootBase, rfl, rfl, rfl⟩
  have ha27 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 26) (.reg 18))))
      { st2 with regs := r3 } .normal { st2 with regs := r4 } 5 :=
    runs_assign_iff.mpr ⟨irVal, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3]))
        (Expr.eval_reg_of_eq (by simp [r3, hregs2 18 (by decide) (by decide) (by decide) (by decide), r1, hr18]))
        (by simp [irBase, isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
      hisRootVal, rfl, rfl, rfl⟩
  have ha28 : Runs w p ω (.assign 28 (.reg 17))
      { st2 with regs := r4 } .normal { st2 with regs := r5 } 2 :=
    runs_assign_iff.mpr ⟨v,
      Expr.eval_reg_of_eq (by simp [r4, r3, hregs2 17 (by decide) (by decide) (by decide) (by decide), r1, hr17]),
      rfl, rfl, rfl⟩
  have hcond_rt : ∃ cRt, Runs w p ω
      (.cond (.bin .eq (.reg 27) (.const 1)) (.assign 28 (.reg 18)) .nop)
      { st2 with regs := r5 } .normal { st2 with regs := r6 } cRt ∧ cRt ≤ 10 := by
    by_cases hv'R : v' ∈ s1.rf.R
    · have hev : (Expr.bin .eq (.reg 27) (.const 1)).eval w { st2 with regs := r5 } = some 1 := by
        simp [Expr.eval, r5, r4, irVal, hv'R, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have ha : Runs w p ω (.assign 28 (.reg 18))
          { st2 with regs := r5 } .normal { st2 with regs := r6 } 2 :=
        runs_assign_iff.mpr ⟨v',
          Expr.eval_reg_of_eq (by simp [r5, r4, r3, hregs2 18 (by decide) (by decide) (by decide) (by decide), r1, hr18]),
          rfl, by simp [r6, rTmp, hv'R], rfl⟩
      exact ⟨_, runs_cond_iff.mpr ⟨1, 2, hev, by simpa using ha, rfl⟩, by simp [Expr.size]⟩
    · have hev : (Expr.bin .eq (.reg 27) (.const 1)).eval w { st2 with regs := r5 } = some 0 := by
        simp [Expr.eval, r5, r4, irVal, hv'R, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hnop : Runs w p ω .nop { st2 with regs := r5 } .normal { st2 with regs := r6 } 1 :=
        runs_nop_iff.mpr ⟨rfl, congrArg (fun r => { st2 with regs := r })
          (funext fun r => by by_cases hr : r = 28 <;> simp [r6, r5, rTmp, hv'R, hr]), rfl⟩
      exact ⟨_, runs_cond_iff.mpr ⟨0, 1, hev, by simpa using hnop, rfl⟩, by simp [Expr.size]⟩
  obtain ⟨cRt, hrunRt, hcRt⟩ := hcond_rt
  -- Step 4: `tourOp 3` (`changeRoot rTmp fresh`)
  have hImpl := (tourDS_implements w vCap eCap p bTour hpT hw).2
  have hrTmpLt : rTmp < vCap := by
    dsimp only [rTmp]; split_ifs; exact hEdit.2.1; exact hEdit.1
  have hargs3 : ∀ a ∈ [tourH, rTmp, fresh, oM.value], a < 2 ^ w := by
    intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl
    · exact htourW
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; omega
    · omega
  have hpre3 : (tourContract vCap eCap tourMul tourAlloc).pre 3 s1 [tourH, rTmp, fresh, oM.value] st2.mem :=
    ⟨tourH, rTmp, fresh, oM.value, rfl, hrTmpR, hfreshLt, hfreshV, hconn⟩
  have hsp3 : oM.value + (tourContract vCap eCap tourMul tourAlloc).space 3 s1
      [tourH, rTmp, fresh, oM.value] st2.mem < 2 ^ w := by
    simp only [tourContract]; unfold tourSplitStepSpace at hroom; omega
  have hzero2' : ZeroFrom st2.mem (heapArg [tourH, rTmp, fresh, oM.value]) := fun a ha => by
    change oM.value ≤ a at ha; exact (hm2_out a (by omega)).trans (hzero1 a ha)
  obtain ⟨bd3, hbd3, o3, st3, c3, hrun3, s3, tx2, hrep2, hpost3, hresp3, hcost3⟩ :=
    hImpl.2.2 3 tourH s1 tx1 [tourH, rTmp, fresh, oM.value] st2.mem st2.pos ω hargs3 rfl
      hrep1_m2 hpre3 hfoot1 hzero2' hsp3
  have hs3_eq : s3 = sWall := by simpa [tourContract] using hpost3
  subst hs3_eq
  have hha3 : heapArg [tourH, rTmp, fresh, oM.value] = oM.value := rfl
  rw [hha3] at hresp3
  simp only [tourContract] at hresp3 hcost3
  have ho3_lo : oM.value ≤ o3.value := hresp3.1
  have ho3_hi : o3.value ≤ oM.value + 2 := hresp3.2.1
  set r7 := Function.update r6 9 o3.value
  have hcall3 : Runs w p ω (.call 9 (tourOp bTour 3) [.reg 0, .reg 28, .reg 25, .reg 9])
      { st2 with regs := r6 } .normal ⟨st3.mem, r7, st3.pos⟩
      (argsSize [.reg 0, .reg 28, .reg 25, .reg 9] + c3 + 1) :=
    runs_call_iff.mpr ⟨_, bd3, o3, st3, c3,
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6, r5, r4, r3, hregs2 0 (by decide) (by decide) (by decide) (by decide), r1, hr0])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6, r5, r4, r3, hr25_2])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6, r5, r4, r3, hregs2 9 (by decide) (by decide) (by decide) (by decide), r1])) <|
      evalArgs_nil _ _,
      hbd3, hrun3, rfl, rfl, rfl⟩
  -- Step 5: shared tail `outSmallSide` + `fConsumeRel`
  have hft12 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a →
      (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < o3.value) := fun a ha => by
    rcases hresp3.2.2.2.2 a ha with h1 | ⟨hge, hlt⟩
    · rcases hft1 a h1 with h0 | ⟨hge0, hlt0⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hge0, by omega⟩
    · exact Or.inr ⟨by omega, hlt⟩
  have hfr12 : ∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a → a ≠ statePtr →
      st3.mem a = st.mem a := fun a ha hnf hneS => by
    have hnf1 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 a := fun hf1 => by
      rcases hft1 a hf1 with h0 | ⟨hge, _⟩
      · exact hnf h0
      · omega
    exact (hresp3.2.2.2.1 a (by omega) hnf1).trans ((hm2_out a hneS).trans (hfr1 a ha hnf))
  have hfoot2 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a → a < o3.value := fun a ha => by
    rcases hft12 a ha with h0 | ⟨_, hlt⟩
    · exact lt_of_lt_of_le (hfoot a h0) (by omega)
    · exact hlt
  have hst2_disj_foot : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx2 (statePtr + i) := fun i hi hf => by
    rcases hft12 (statePtr + i) hf with h0 | ⟨hge, _⟩
    · exact hst_disj_foot i hi h0
    · omega
  have hsp2_disj : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length →
      ¬ (tourAsmRep vCap eCap).foot tourH tx2 a := fun a ha1 ha2 hf => by
    rcases hft12 a hf with h0 | ⟨hge, _⟩
    · exact hsp_disj a ha1 ha2 h0
    · omega
  have hspAt2 : SplitEntriesAt st3.mem spPtr L :=
    asmFirstSplitEntriesAt_congr hspAt fun a ha1 ha2 =>
      hfr12 a (by omega) (hsp_disj a ha1 ha2) (by omega)
  have hnf1S : ¬ (tourAsmRep vCap eCap).foot tourH tx1 statePtr := by
    have := hst1_disj_foot 0 (by decide); rwa [Nat.add_zero] at this
  have hst2_mem' : st3.mem statePtr = spIdx + 1 ∧ st3.mem (statePtr + 1) = splitPtr ∧
      st3.mem (statePtr + 2) = last :=
    ⟨(hresp3.2.2.2.1 statePtr (by omega) hnf1S).trans
        (by rw [hst2_mem, Function.update_self]),
     (hfr12 (statePtr + 1) (by omega) (hst_disj_foot 1 (by decide)) (by omega)).trans hst_mem.2.1,
     (hfr12 (statePtr + 2) (by omega) (hst_disj_foot 2 (by decide)) (by omega)).trans hst_mem.2.2⟩
  have hpre2 := outSplitPrefixAt_mono
    (avoid' := fun a => (tourAsmRep vCap eCap).foot tourH tx2 a ∨ a < statePtr + 3)
    hpre (by omega : hCur ≤ o3.value)
    (fun a ha hna h2' => by
      rcases h2' with hf | hex
      · rcases hft12 a hf with h0 | ⟨hge, _⟩
        · exact hna (Or.inl h0)
        · omega
      · exact hna (Or.inr hex))
    (fun a ha hna => hfr12 a ha (fun hf => hna (Or.inl hf))
      (fun hEq => hna (Or.inr (by omega))))
  have hroomTail : o3.value + outSmallSideSpace tourOutSpec (2 * eCap) +
      relL.length * tourSplitStepSpace eCap + 2 < 2 ^ w := by
    have : (1 + relL.length) * tourSplitStepSpace eCap =
        2 + outSmallSideSpace tourOutSpec (2 * eCap) + relL.length * tourSplitStepSpace eCap := by
      rw [Nat.add_mul, Nat.one_mul]; unfold tourSplitStepSpace; omega
    omega
  obtain ⟨hEnd, stF, cTail, txF, splitPtrF, lastF, Y, YsRel, hrunTail, hr9F, hregsF,
    hrepF, hMF, hKF, hstF0, hstF1, hstF2, hlstF, hpreF, hpotF, hhEndLo, hhEndHi, hzeroF, hfrTail, hftTail, hcostTail⟩ :=
    tourBlock_smallSide_and_rel_runs hpT hpO hpRel hw
      (sPrev := s) (sWall := sWall) (tx2 := tx2) (st := ⟨st3.mem, r7, st3.pos⟩)
      (spIdx := spIdx) (splitPtr := splitPtr) (last := last)
      (by simp [r7, r6, r5, r4, r3, hregs2 0 (by decide) (by decide) (by decide) (by decide), r1, hr0])
      (by simp [r7, r6, r5, r4, r3, hregs2 5 (by decide) (by decide) (by decide) (by decide), r1, hr5])
      (by simp [r7, r6, r5, r4, r3, hregs2 7 (by decide) (by decide) (by decide) (by decide), r1, hr7])
      (by simp [r7])
      (by simp [r7, r6, r5, r4, r3, hregs2 10 (by decide) (by decide) (by decide) (by decide), r1, hr10])
      (by simp [r7, r6, r5, r4, r3, hr24_2])
      (by simp [r7, r6, r5, r4, r3, hr25_2])
      hrep2 hfoot2 hresp3.2.2.1 hspAt2 (by omega) hsp2_disj hst2_mem' (by omega) hst2_disj_foot
      hst_disj_sp hst_disj_last hsp_disj_last hspIdx_lt hdrop1 hrest_stop
      hkeptLt hfreshLt hkeptR hfreshNotR hR'_eq hother2 hunion2 hM2 hkM hME₀ hK2 hpre2 hchain hroomTail
  have hrunMid := runs_seq_normal ha26 (runs_seq_normal ha27 (runs_seq_normal ha28
    (runs_seq_normal hrunRt (runs_seq_normal hcall3 hrunTail))))
  have hrunFlat := runs_seq_normal hcallM (walls_runs_seq_r5 (runs_seq_normal hrunPop hrunMid))
  have hspTot : hEnd ≤ hCur + (13 * m + 77) + (1 + relL.length) * tourSplitStepSpace eCap := by
    have : (1 + relL.length) * tourSplitStepSpace eCap =
        2 + outSmallSideSpace tourOutSpec (2 * eCap) + relL.length * tourSplitStepSpace eCap := by
      rw [Nat.add_mul, Nat.one_mul]; unfold tourSplitStepSpace; omega
    omega
  refine ⟨hEnd, stF, _, txF, splitPtrF, lastF, Y, YsRel, hrunFlat, hr9F,
    fun r h9 h22 h23 h24 h25 h26 h27 h28 =>
      (hregsF r h9 h26 h27).trans (by simp [r7, r6, r5, r4, r3, h9, h26, h27, h28,
        hregs2 r h22 h23 h24 h25, r1]),
    hrepF, hMF, hKF, hstF0, hstF1, hstF2, by omega, hpreF, hpotF, by omega, hspTot, hzeroF,
    fun a ha hnf hstO hnl =>
      (hfrTail a (by omega) (fun hf => by
        rcases hft12 a hf with h0 | ⟨hge, _⟩
        · exact hnf h0
        · omega) hstO hnl).trans (hfr12 a ha hnf (by omega)),
    fun a ha => by
      rcases hftTail a ha with h1 | ⟨hge, hlt⟩
      · rcases hft12 a h1 with h0 | ⟨hge0, hlt0⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hge0, by omega⟩
      · exact Or.inr ⟨by omega, hlt⟩, ?_⟩
  have hphi2 : (tourDSRep vCap eCap).phi tourH tx1 stM.mem = (tourDSRep vCap eCap).phi tourH tx1 st2.mem := hloc2.2
  have hphi_s3 : (tourAsmRep vCap eCap).phi tourH tx2 st3.mem = (tourDSRep vCap eCap).phi tourH tx2 st3.mem ∧
      (tourAsmRep vCap eCap).phi tourH tx1 stM.mem = (tourDSRep vCap eCap).phi tourH tx1 stM.mem := ⟨rfl, rfl⟩
  rw [← hphi2, ← ordStoreLog_eq_tourLog] at hcost3
  rw [hphi_s3.2] at hcostM
  rw [hphi_s3.1] at hcostTail
  set S_tot := Y.length + (YsRel.map List.length).sum + (1 + relL.length) + (4 + m) + 5
  have hmove_le : tourApplyMoveMul * (4 + m + 2) * ordStoreLog eCap ≤
      tourApplyMoveMul * S_tot * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hc3_le : tourMul * ordStoreLog eCap ≤ 5 * tourMul * S_tot * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (le_trans (by omega : tourMul ≤ 5 * tourMul)
      (Nat.le_mul_of_pos_right _ (by omega)))
  have htail_le : (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) *
      (Y.length + (YsRel.map List.length).sum + (1 + relL.length) + 1) * ordStoreLog eCap ≤
      (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) * S_tot * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hov : 150 ≤ 420 * S_tot * ordStoreLog eCap :=
    le_trans (by omega : 150 ≤ 420 * S_tot) (Nat.le_mul_of_pos_right _ htl)
  have hbm : 5 * tourMul * S_tot * ordStoreLog eCap +
      (outSmallSideMul * (tourOutSpec.mul + 1) + tourConsumeRelMul + 80) * S_tot * ordStoreLog eCap +
      tourApplyMoveMul * S_tot * ordStoreLog eCap + 420 * S_tot * ordStoreLog eCap ≤
      tourBlockCaseMul * S_tot * ordStoreLog eCap := by
    rw [tourBlockCaseMul_eq, tourBlockCaseMulFn_eq]
    rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  simp only [argsSize, Expr.size]
  clear * - hcostM hcPop hcRt hcost3 hcostTail hmove_le hc3_le htail_le hov hbm
  omega

end

end MinCostFlow.SparseCore.Program
