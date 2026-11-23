module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepProg

import Mathlib.Tactic

/-!
# Verification of the release-consumer loop (`AssemblyFirstTourStepRel`)

Defines `TourRelChain` (inductive validity and split correspondence for a contiguous slice of
`isRelease = true` entries) and verifies Helper 1 (`asmFirstTourConsumeRelStmt`,
`asmFirstTourConsumeRel_runs`) directly from `tourDS_implements` (op `1`, `cut`) and
`sig_outSmallSide_runs_outProcs` (`outSmallSideMul_spec`), advancing `tourAsmRep`,
`OutSplitPrefixAt`, `TourMarksAt`, `TourKeepMatch`, and telescoping `tourMarkPot`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. Inductive release-chain specification `TourRelChain` -/

@[expose] public section

/-- Inductive specification for consuming a contiguous sequence `relL` of `isRelease = true`
entries from `s₀` / `S₀` to `s_f` / `S_f`, matched 1-to-1 with the restricted core splits `P_rel`. -/
inductive TourRelChain (vCap eCap : ℕ) (keep M : Finset ℕ) :
    TourAbs → MGraph → List CompSplitEntry → List Update → TourAbs → MGraph → Prop
  | nil (s : TourAbs) (S : MGraph) :
      TourRelChain vCap eCap keep M s S [] [] s S
  | cons {e kept fresh : ℕ} {St Sh : Finset ℕ} {s s_f : TourAbs} {S S_f : MGraph}
      {rels : List CompSplitEntry} {Ps : List Update}
      (he : e ∈ s.rf.F.E) (heM : e ∉ M)
      (hkept_eq : kept = s.rf.root (s.rf.F.tail e))
      (hfreshLt : fresh < vCap) (hfreshV : fresh ∈ s.rf.F.V) (hfreshNotR : fresh ∉ s.rf.R)
      (huniq' : ∀ v ∈ s.rf.F.V,
        ∃! r, r ∈ insert fresh s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r)
      (hSt : ∀ f ∈ keep, f ∈ St ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, true)) = fresh)
      (hSh : ∀ f ∈ keep, f ∈ Sh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, false)) = fresh)
      (hrest : TourRelChain vCap eCap keep M
        (tourCut s e fresh) (S.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep)))
        rels Ps s_f S_f) :
      TourRelChain vCap eCap keep M s S
        (⟨true, e, kept, fresh⟩ :: rels)
        (.split kept fresh (St ∩ keep) (Sh ∩ keep) :: Ps)
        s_f S_f

end

private theorem tourRelChain_all_true {vCap eCap : ℕ} {keep M : Finset ℕ}
    {s s_f : TourAbs} {S S_f : MGraph} {rels : List CompSplitEntry} {Ps : List Update}
    (h : TourRelChain vCap eCap keep M s S rels Ps s_f S_f) :
    ∀ r ∈ rels, r.isRelease = true := by
  induction h with
  | nil _ _ => intro _ hr; cases hr
  | cons _ _ _ _ _ _ _ _ _ _ ih =>
    intro r hr; rcases List.mem_cons.mp hr with rfl | h'; exact rfl; exact ih r h'

/-! ## 2. Verification of `asmFirstTourConsumeRelStmt` -/

public section

/-- Single-step helper: runs `tourOp 1` (`cut e fresh`) followed by `outIdxSmallSide` on
`(kept, fresh)`, advancing `tourAsmRep`, `OutSplitPrefixAt`, `TourMarksAt`, `TourKeepMatch`,
and `tourMarkPot` (preserving an arbitrary extra avoid predicate `extraAv` lying below `hCur`). -/
theorem tourCut_and_smallSide_runs {w vCap eCap bTour bOut tourH e kept fresh last hCur pos : ℕ}
    {p : Program} (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {s : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    {keep M E₀ St Sh : Finset ℕ} {G₀ S_cur : MGraph} {extraAv : ℕ → Prop}
    {splitPtr : ℕ} {P_done : List Update} {Ys_done : List (List End)}
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < hCur)
    (hextra : ∀ a, extraAv a → a < hCur) (hzero : ZeroFrom mem hCur)
    (hM : TourMarksAt s M) (hkM : keep ⊆ M) (hME₀ : M ⊆ E₀) (hK : TourKeepMatch keep s S_cur)
    (hpre : OutSplitPrefixAt mem splitPtr last hCur
      (fun a => (tourAsmRep vCap eCap).foot tourH tx a ∨ extraAv a) keep E₀ G₀ P_done S_cur Ys_done)
    (he : e ∈ s.rf.F.E) (heM : e ∉ M)
    (hkept_eq : kept = s.rf.root (s.rf.F.tail e))
    (hfreshLt : fresh < vCap) (hfreshV : fresh ∈ s.rf.F.V) (hfreshNotR : fresh ∉ s.rf.R)
    (huniq' : ∀ v ∈ s.rf.F.V,
      ∃! r, r ∈ insert fresh s.rf.R ∧ (eraseForestEdge s.rf.F e).Connected v r)
    (hSt : ∀ f ∈ keep, f ∈ St ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, true)) = fresh)
    (hSh : ∀ f ∈ keep, f ∈ Sh ↔ (tourCut s e fresh).rf.root (ordSrc s.ord (f, false)) = fresh)
    (hroom : hCur + tourSplitStepSpace eCap < 2 ^ w) :
    let s' := tourCut s e fresh
    let S' := S_cur.applyUpdate (.split kept fresh (St ∩ keep) (Sh ∩ keep))
    ∃ bdCut, p.procs[tourOp bTour 1]? = some bdCut ∧
    ∃ bdSS, p.procs[outIdxSmallSide bOut]? = some bdSS ∧
    ∃ o1 st1 c1 o2 st2 c2 tx2 Y,
      Runs w p ω bdCut (startState [tourH, e, fresh, hCur] mem pos) o1 st1 c1 ∧
      Runs w p ω bdSS
        (startState [tourH, kept, fresh, kept, fresh, last, o1.value] st1.mem st1.pos) o2 st2 c2 ∧
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s') tx2 st2.mem ∧
      TourMarksAt s' M ∧
      TourKeepMatch keep s' S' ∧
      OutSplitPrefixAt st2.mem (if splitPtr = 0 then o1.value else splitPtr) o1.value o2.value
        (fun a => (tourAsmRep vCap eCap).foot tourH tx2 a ∨ extraAv a) keep E₀ G₀
        (P_done ++ [.split kept fresh (St ∩ keep) (Sh ∩ keep)]) S' (Ys_done ++ [Y]) ∧
      Y.length + tourMarkPot keep s' ≤ min (S'.deg kept) (S'.deg fresh) + tourMarkPot keep s ∧
      hCur ≤ o1.value ∧ o1.value ≤ hCur + 2 ∧
      o1.value + 5 ≤ o2.value ∧ o2.value ≤ hCur + tourSplitStepSpace eCap ∧
      ZeroFrom st2.mem o2.value ∧
      (∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a → (last = 0 ∨ a ≠ last + 4) →
        st2.mem a = mem a) ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a →
        (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < o2.value)) ∧
      c1 + c2 + (tourAsmRep vCap eCap).phi tourH tx2 st2.mem ≤
        (tourMul + outSmallSideMul * (tourOutSpec.mul + 1)) * (Y.length + 1) * ordStoreLog eCap +
          (tourAsmRep vCap eCap).phi tourH tx mem := by
  intro s' S'
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx mem at hrep
  have hord_le : ordHandleOf tourH vCap eCap ≤ hCur := hrep.fixed_le_heap hfoot
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by unfold tourSplitStepSpace at hroom; omega)).2
  have hsync := tourCut_split_sync hrep.valid hM hK he heM hkept_eq hfreshV hfreshNotR huniq' hSt hSh
  obtain ⟨hv', hM', hK', hkeptR, hother, hunion⟩ := hsync
  have hkeptLt : kept < vCap := hrep.valid.verts_lt kept (hrep.valid.roots_sub hkeptR)
  have heLt : e < eCap := hrep.valid.ordWithin.2.2 _ (e, true) (hrep.valid.compat.forestEnd e he).1
  have htourW : tourH < 2 ^ w := lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by unfold tourSplitStepSpace at hroom; omega)
  have hImpl := (tourDS_implements w vCap eCap p bTour hpT hw).2
  have hargs1 : ∀ a ∈ [tourH, e, fresh, hCur], a < 2 ^ w := by
    intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl <;>
      first | exact htourW | (simp [ordHandleOf, tourFixedSize] at hord_le; unfold tourSplitStepSpace at hroom; omega)
  have hpre1 : (tourContract vCap eCap tourMul tourAlloc).pre 1 s [tourH, e, fresh, hCur] mem :=
    ⟨tourH, e, fresh, hCur, rfl, he, hfreshLt, hfreshV, hfreshNotR, huniq'⟩
  have hsp1 : hCur + (tourContract vCap eCap tourMul tourAlloc).space 1 s [tourH, e, fresh, hCur] mem < 2 ^ w := by
    simp only [tourContract]; unfold tourSplitStepSpace at hroom; omega
  obtain ⟨bdCut, hbdCut, o1, st1, c1, hrun1, s1, tx1, hrep1, hpost1, hresp1, hcost1⟩ :=
    hImpl.2.2 1 tourH s tx [tourH, e, fresh, hCur] mem pos ω hargs1 rfl hrep hpre1 hfoot hzero hsp1
  have hs1_eq : s1 = s' := by simpa [tourContract] using hpost1
  subst hs1_eq
  have hha1 : heapArg [tourH, e, fresh, hCur] = hCur := rfl
  rw [hha1] at hresp1
  have ho1_lo : hCur ≤ o1.value := hresp1.1
  have ho1_hi : o1.value ≤ hCur + 2 := hresp1.2.1
  have hfoot1 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx1 a → a < o1.value := fun a ha => by
    rcases hresp1.2.2.2.2 a ha with h0 | ⟨_, h2⟩
    · exact lt_of_lt_of_le (hfoot a h0) ho1_lo
    · exact h2
  have ho1_pos : 0 < o1.value := by
    have : tourH < hCur := hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)
    omega
  have hlast_ok : last = 0 ∨ (last + 4 < o1.value ∧ ¬ (tourAsmRep vCap eCap).foot tourH tx1 (last + 4)) := by
    by_cases hP : P_done = []
    · exact Or.inl (hpre.2.1 hP).2.1
    · obtain ⟨_, _, hl5, hlav, _⟩ := hpre.2.2.1 hP
      refine Or.inr ⟨by omega, fun hf1 => ?_⟩
      rcases hresp1.2.2.2.2 (last + 4) hf1 with h0 | ⟨hge, _⟩
      · exact hlav (Or.inl h0)
      · omega
  -- Call `outSmallSide` using `tourPinnedOutAt` (preserves `s'.ord` and `s'.rf` identically)
  let T := tourPinnedOutAt w vCap eCap p bTour hpT s'.ord s'.rf
  set sOut : OutTourAbs := ⟨coreTour s'.ord s'.rf, s'.marked⟩
  have hrepOut1 : T.rep.rep tourH sOut tx1 st1.mem := ⟨rfl, hrep1⟩
  have hndK : (sOut.cord kept).Nodup := by
    by_cases hr : kept ∈ s'.rf.R
    · show (coreTour s'.ord s'.rf kept).Nodup
      rw [← fullTour_filter_open s'.ord hv'.compat.forest hr]
      exact (fullTour_spec hv'.compat kept).1.filter _
    · simp [sOut, coreTour, hr]
  have hndF : (sOut.cord fresh).Nodup := by
    by_cases hr : fresh ∈ s'.rf.R
    · show (coreTour s'.ord s'.rf fresh).Nodup
      rw [← fullTour_filter_open s'.ord hv'.compat.forest hr]
      exact (fullTour_spec hv'.compat fresh).1.filter _
    · simp [sOut, coreTour, hr]
  have hml_lt : ∀ x ∈ sOut.markedList kept ++ sOut.markedList fresh, x.1 < eCap := by
    intro x hx
    have hmem : x ∈ tourMarkedList s' kept ∨ x ∈ tourMarkedList s' fresh := by
      simpa [sOut, OutTourAbs.markedList, tourMarkedList] using hx
    rcases hmem with h1 | h2
    · obtain ⟨_, ⟨u, hu⟩, _, _, _⟩ := (mem_tourMarkedList_iff hv' hM' kept x).mp h1
      exact hv'.ordWithin.2.2 u x hu
    · obtain ⟨_, ⟨u, hu⟩, _, _, _⟩ := (mem_tourMarkedList_iff hv' hM' fresh x).mp h2
      exact hv'.ordWithin.2.2 u x hu
  have hargs2 : ∀ a ∈ [tourH, kept, fresh, kept, fresh, last, o1.value], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact htourW
    · simp [ordHandleOf, tourFixedSize] at hord_le; unfold tourSplitStepSpace at hroom; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; unfold tourSplitStepSpace at hroom; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; unfold tourSplitStepSpace at hroom; omega
    · simp [ordHandleOf, tourFixedSize] at hord_le; unfold tourSplitStepSpace at hroom; omega
    · rcases hlast_ok with rfl | ⟨hl, _⟩
      · omega
      · unfold tourSplitStepSpace at hroom; omega
    · unfold tourSplitStepSpace at hroom; omega
  have hsp2 : o1.value + outSmallSideSpace tourOutSpec (2 * eCap) < 2 ^ w := by
    unfold tourSplitStepSpace at hroom; omega
  obtain ⟨bdSS, hbdSS, o2, st2, c2, tx2, hrun2, hrepOut2, hm0, hm1, hm2, hm4, hEL, _,
    hptr5, ho2_eq, ho2_le, hzero2, hpatch2, hfr2, hft2, hcost2⟩ :=
    outSmallSideMul_spec tourOutSpec w vCap eCap p bOut (tourOp bTour 8) (tourOp bTour 7)
      (tourOp bTour 11) (tourOp bTour 9) hpO hw T tourH kept fresh kept fresh last o1.value
      sOut tx1 st1.mem st1.pos ω hargs2 hkeptLt hfreshLt hndK hndF hml_lt
      hrepOut1 hfoot1 ho1_pos hlast_ok hresp1.2.2.1 hsp2
  have hrep2 : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s') tx2 st2.mem := hrepOut2.2
  set side := if (tourMarkedList s' kept).length ≤ (tourMarkedList s' fresh).length then 0 else 1
  set Y := tourMarkedList s' (if side = 0 then kept else fresh)
  have ho2_eq' : o2.value = st2.mem (o1.value + 3) + 1 + Y.length := ho2_eq
  have hsplit := tourMarkPot_split_step hv' hM' hkM hME₀ hK' hkeptR hfreshNotR rfl hother hunion
  obtain ⟨hndY, hYE, hYkeep, hpot⟩ := hsplit
  have hpre1 : OutSplitPrefixAt st1.mem splitPtr last o1.value
      (fun a => (tourAsmRep vCap eCap).foot tourH tx1 a ∨ extraAv a) keep E₀ G₀ P_done S_cur Ys_done :=
    outSplitPrefixAt_mono hpre ho1_lo
      (fun a ha hna h1 => by
        rcases h1 with hf1 | hex
        · rcases hresp1.2.2.2.2 a hf1 with h0 | ⟨hge, _⟩
          · exact hna (Or.inl h0)
          · omega
        · exact hna (Or.inr hex))
      (fun a ha hna => hresp1.2.2.2.1 a ha (fun hf => hna (Or.inl hf)))
  have hpre2 := outSplitPrefixAt_snoc (ptr := st2.mem (o1.value + 3)) (Y := Y)
    (avoid' := fun a => (tourAsmRep vCap eCap).foot tourH tx2 a ∨ extraAv a)
    hpre1 ho1_pos (le_refl _) hptr5 ho2_eq'.symm.le
    (fun a ha hna h2 => by
      rcases h2 with hf2 | hex
      · rcases hft2 a hf2 with h1 | ⟨hge, _⟩
        · exact hna (Or.inl h1)
        · omega
      · exact hna (Or.inr hex))
    (fun i hi h2 => by
      rcases h2 with hf2 | hex
      · rcases hft2 (o1.value + i) hf2 with h1 | ⟨hge, _⟩
        · exact absurd (hfoot1 _ h1) (by omega)
        · omega
      · exact absurd (hextra _ hex) (by omega))
    (fun i hi h2 => by
      rcases h2 with hf2 | hex
      · rcases hft2 (st2.mem (o1.value + 3) + i) hf2 with h1 | ⟨_, hlt⟩
        · exact absurd (hfoot1 _ h1) (by omega)
        · omega
      · exact absurd (hextra _ hex) (by omega))
    (fun a ha hna hneL => hfr2 a ha (fun hf => hna (Or.inl hf)) hneL)
    hpatch2 hm0 hm1 hm2 (by change (if _ then 0 else 1) ≤ 1; split_ifs <;> omega) rfl hm4 hEL hndY hYE hYkeep
  have hft_all : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a →
      (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < o2.value) := fun a ha => by
    rcases hft2 a ha with h1 | ⟨hge, hlt⟩
    · rcases hresp1.2.2.2.2 a h1 with h0 | ⟨hge1, hlt1⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hge1, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hfr_all : ∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a →
      (last = 0 ∨ a ≠ last + 4) → st2.mem a = mem a := fun a ha hnf hneL => by
    have hnf1 : ¬ (tourAsmRep vCap eCap).foot tourH tx1 a := fun hf1 => by
      rcases hresp1.2.2.2.2 a hf1 with h0 | ⟨hge, _⟩
      · exact hnf h0
      · omega
    exact (hfr2 a (by omega) hnf1 hneL).trans (hresp1.2.2.2.1 a ha hnf)
  refine ⟨bdCut, hbdCut, bdSS, hbdSS, o1, st1, c1, o2, st2, c2, tx2, Y,
    hrun1, hrun2, hrep2, hM', hK', hpre2, hpot, ho1_lo, ho1_hi, by omega,
    by unfold tourSplitStepSpace; omega, hzero2, hfr_all, hft_all, ?_⟩
  have hcost1' : c1 + (tourAsmRep vCap eCap).phi tourH tx1 st1.mem ≤
      tourMul * ordStoreLog eCap + (tourAsmRep vCap eCap).phi tourH tx mem := by
    simp only [tourContract] at hcost1; rw [ordStoreLog_eq_tourLog]; exact hcost1
  have hcost2' : c2 + (tourAsmRep vCap eCap).phi tourH tx2 st2.mem ≤
      outSmallSideMul * (tourOutSpec.mul + 1) * (Y.length + 1) * ordStoreLog eCap +
        (tourAsmRep vCap eCap).phi tourH tx1 st1.mem := hcost2
  set yLen := Y.length
  have h1m : tourMul * ordStoreLog eCap ≤ tourMul * (yLen + 1) * ordStoreLog eCap :=
    calc tourMul * ordStoreLog eCap = tourMul * 1 * ordStoreLog eCap := by simp
      _ ≤ tourMul * (yLen + 1) * ordStoreLog eCap :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.succ_pos _))
  have hdist : (tourMul + outSmallSideMul * (tourOutSpec.mul + 1)) * (yLen + 1) * ordStoreLog eCap =
      tourMul * (yLen + 1) * ordStoreLog eCap +
        outSmallSideMul * (tourOutSpec.mul + 1) * (yLen + 1) * ordStoreLog eCap := by ring
  omega

/-- Helper: 1-step `cont` check (`r8 := 0; if r5 < r2 then r8 := mem[spPtr + 1 + 4*r5]`). -/
private theorem consumeRel_check_runs {w spPtr : ℕ} {p : Program} {ω : ℕ → Bool}
    {L spRest : List CompSplitEntry}
    (hwide : 18 ≤ 2 ^ w) (hsp_w : spPtr + 1 + 4 * L.length < 2 ^ w)
    (hrest_stop : ∀ e rest, spRest = e :: rest → e.isRelease = false)
    (st : State) (idx : ℕ) (rel : List CompSplitEntry)
    (hr1 : st.regs 1 = spPtr) (hr2 : st.regs 2 = L.length) (hr5 : st.regs 5 = idx)
    (hidx_le : idx ≤ L.length) (hdr : L.drop idx = rel ++ spRest)
    (hrel_t : ∀ r ∈ rel, r.isRelease = true)
    (hspC : SplitEntriesAt st.mem spPtr L) :
    ∃ st1 c1,
      Runs w p ω (.assign 8 (.const 0) ;;
        .cond (.bin .lt (.reg 5) (.reg 2))
          (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1))
            (.bin .mul (.const 4) (.reg 5)))))
          .nop) st .normal st1 c1 ∧
      st1.mem = st.mem ∧
      (∀ r ≠ 8, st1.regs r = st.regs r) ∧
      st1.regs 8 = (if rel = [] then 0 else 1) ∧
      c1 ≤ 25 := by
  set rA := Function.update st.regs 8 0
  have ha0 : Runs w p ω (.assign 8 (.const 0)) st .normal { st with regs := rA } 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  by_cases hlt : idx < L.length
  · have hcond : (Expr.bin .lt (.reg 5) (.reg 2)).eval w { st with regs := rA } = some 1 := by
      simp [Expr.eval, rA, hr5, hr2, hlt, BinOp.eval, (by omega : 1 < 2 ^ w)]
    have hent := hspC.2 idx hlt
    have hflag : (if L[idx].isRelease then 1 else 0) = (if rel = [] then 0 else 1) := by
      have hhd : L[idx] :: L.drop (idx + 1) = rel ++ spRest := by
        rw [← List.drop_eq_getElem_cons hlt, hdr]
      cases rel with
      | nil =>
        simp only [List.nil_append] at hhd
        have hf := hrest_stop L[idx] (L.drop (idx + 1)) hhd.symm
        simp [hf]
      | cons e0 es0 =>
        simp only [List.cons_append, List.cons.injEq] at hhd
        have ht := hrel_t e0 List.mem_cons_self
        rw [hhd.1, ht]; simp
    set rB := Function.update rA 8 (if rel = [] then 0 else 1)
    have haL : Runs w p ω
        (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1))
          (.bin .mul (.const 4) (.reg 5)))))
        { st with regs := rA } .normal { st with regs := rB } 9 :=
      runs_assign_iff.mpr ⟨if rel = [] then 0 else 1,
        Expr.eval_load_of_eq
          (Expr.eval_add
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr1]))
              (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (by simp [rA, hr5])) (by omega))
            (by omega))
          (hent.1.trans hflag), rfl, rfl, rfl⟩
    have hrc : Runs w p ω
        (.cond (.bin .lt (.reg 5) (.reg 2))
          (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1))
            (.bin .mul (.const 4) (.reg 5)))))
          .nop) { st with regs := rA } .normal { st with regs := rB } (3 + 9 + 1) :=
      runs_cond_iff.mpr ⟨1, 9, hcond, by simpa using haL, rfl⟩
    refine ⟨{ st with regs := rB }, _, runs_seq_normal ha0 hrc,
      rfl, fun r hr => by simp [rB, rA, hr], by simp [rB], by omega⟩
  · have hrel_nil : rel = [] := by
      have hdrop_nil : L.drop idx = [] := List.drop_eq_nil_of_le (by omega)
      rw [hdrop_nil] at hdr
      exact (List.append_eq_nil_iff.mp hdr.symm).1
    have hcond : (Expr.bin .lt (.reg 5) (.reg 2)).eval w { st with regs := rA } = some 0 := by
      simp [Expr.eval, rA, hr5, hr2, hlt, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hrc : Runs w p ω
        (.cond (.bin .lt (.reg 5) (.reg 2))
          (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1))
            (.bin .mul (.const 4) (.reg 5)))))
          .nop) { st with regs := rA } .normal { st with regs := rA } (3 + 1 + 1) :=
      runs_cond_iff.mpr ⟨0, 1, hcond,
        by simpa using (runs_nop_iff (w := w) (p := p) (ω := ω)).mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    refine ⟨{ st with regs := rA }, _, runs_seq_normal ha0 hrc,
      rfl, fun r hr => by simp [rA, hr], by simp [rA, hrel_nil], by omega⟩

/-- Helper: inductive verification of the `while r8 ≠ 0` loop of `asmFirstTourConsumeRelStmt`. -/
private theorem consumeRel_loop_runs {w vCap eCap bTour bOut tourH spPtr statePtr : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hwide : 18 ≤ 2 ^ w) (_htourW : tourH < 2 ^ w)
    {L spRest : List CompSplitEntry}
    (hsp_w : spPtr + 1 + 4 * L.length < 2 ^ w)
    (hrest_stop : ∀ e rest, spRest = e :: rest → e.isRelease = false)
    {keep M E₀ : Finset ℕ} {G₀ : MGraph} (hkM : keep ⊆ M) (hME₀ : M ⊆ E₀)
    {s0 s_f : TourAbs} {S0 S_f : MGraph} {rels : List CompSplitEntry} {Ps : List Update}
    (hch : TourRelChain vCap eCap keep M s0 S0 rels Ps s_f S_f) :
    ∀ {idx spP lst hC : ℕ} {tx0 : (tourAsmRep vCap eCap).τ} {st0 : State}
      {Pd : List Update} {Ysd : List (List End)},
      st0.regs 0 = tourH → st0.regs 1 = spPtr → st0.regs 2 = L.length →
      st0.regs 3 = statePtr → st0.regs 4 = hC →
      st0.regs 5 = idx → st0.regs 6 = spP → st0.regs 7 = lst →
      st0.regs 8 = (if rels = [] then 0 else 1) →
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s0) tx0 st0.mem →
      (∀ a, (tourAsmRep vCap eCap).foot tourH tx0 a → a < hC) →
      ZeroFrom st0.mem hC →
      SplitEntriesAt st0.mem spPtr L →
      spPtr + 1 + 4 * L.length ≤ hC →
      (∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → ¬ (tourAsmRep vCap eCap).foot tourH tx0 a) →
      (lst = 0 ∨ lst + 4 < spPtr ∨ spPtr + 1 + 4 * L.length ≤ lst + 4) →
      idx ≤ L.length → L.drop idx = rels ++ spRest →
      TourMarksAt s0 M → TourKeepMatch keep s0 S0 →
      OutSplitPrefixAt st0.mem spP lst hC
        (fun a => (tourAsmRep vCap eCap).foot tourH tx0 a ∨ a < statePtr + 3)
        keep E₀ G₀ Pd S0 Ysd →
      statePtr + 3 ≤ hC →
      hC + rels.length * tourSplitStepSpace eCap < 2 ^ w →
      ∃ hE stF cL txF spF lstF YsR,
        Runs w p ω (.loop (.reg 8)
          (.assign 9 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 5))) ;;
           .assign 10 (.load (.bin .add (.reg 9) (.const 1))) ;;
           .assign 11 (.load (.bin .add (.reg 9) (.const 2))) ;;
           .assign 12 (.load (.bin .add (.reg 9) (.const 3))) ;;
           .call 4 (tourOp bTour 1) [.reg 0, .reg 10, .reg 12, .reg 4] ;;
           .assign 13 (.reg 4) ;;
           .call 4 (outIdxSmallSide bOut) [.reg 0, .reg 11, .reg 12, .reg 11, .reg 12, .reg 7, .reg 13] ;;
           .cond (.bin .eq (.reg 6) (.const 0)) (.assign 6 (.reg 13)) .nop ;;
           .assign 7 (.reg 13) ;;
           .assign 5 (.bin .add (.reg 5) (.const 1)) ;;
           .assign 8 (.const 0) ;;
           .cond (.bin .lt (.reg 5) (.reg 2))
             (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1))
               (.bin .mul (.const 4) (.reg 5)))))
             .nop)) st0 .normal stF cL ∧
        stF.regs 3 = statePtr ∧ stF.regs 4 = hE ∧ stF.regs 5 = idx + rels.length ∧
        stF.regs 6 = spF ∧ stF.regs 7 = lstF ∧ (lstF = lst ∨ hC ≤ lstF) ∧
        (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s_f) txF stF.mem ∧
        TourMarksAt s_f M ∧ TourKeepMatch keep s_f S_f ∧
        OutSplitPrefixAt stF.mem spF lstF hE
          (fun a => (tourAsmRep vCap eCap).foot tourH txF a ∨ a < statePtr + 3)
          keep E₀ G₀ (Pd ++ Ps) S_f (Ysd ++ YsR) ∧
        (YsR.map List.length).sum + tourMarkPot keep s_f ≤
          S0.batchEnc Ps + tourMarkPot keep s0 ∧
        hC ≤ hE ∧ hE ≤ hC + rels.length * tourSplitStepSpace eCap ∧ ZeroFrom stF.mem hE ∧
        (∀ a < hC, ¬ (tourAsmRep vCap eCap).foot tourH tx0 a → (lst = 0 ∨ a ≠ lst + 4) →
          stF.mem a = st0.mem a) ∧
        (∀ a, (tourAsmRep vCap eCap).foot tourH txF a →
          (tourAsmRep vCap eCap).foot tourH tx0 a ∨ (hC ≤ a ∧ a < hE)) ∧
        cL + (tourAsmRep vCap eCap).phi tourH txF stF.mem ≤
          tourConsumeRelMul * ((YsR.map List.length).sum + rels.length) * ordStoreLog eCap + 4 +
            (tourAsmRep vCap eCap).phi tourH tx0 st0.mem := by
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  induction hch with
    | nil s0 S0 =>
      intro idx spP lst hC tx0 st0 Pd Ysd _ _ _ hr3 hr4 hr5 hr6 hr7 hr8 hrep0 _ hz0 _ _ _ _ _ _
        hM0 hK0 hpre0 _ _
      have hcond0 : (Expr.reg 8).eval w st0 = some 0 := Expr.eval_reg_of_eq (by simpa using hr8)
      refine ⟨hC, st0, 2, tx0, spP, lst, [],
        runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, rfl⟩),
        hr3, hr4, by omega, hr6, hr7, Or.inl rfl, hrep0, hM0, hK0,
        by simpa using hpre0, by simp, le_refl _, by simp, hz0,
        fun _ _ _ _ => rfl, fun _ ha => Or.inl ha, by omega⟩
    | @cons e kept fresh St Sh s0 _ S0 _ rels' Ps' he heM hkept_eq hfreshLt hfreshV hfreshNotR
        huniq' hSt hSh hrest ih =>
      intro idx spP lst hC tx0 st0 Pd Ysd hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8
        hrep0 hfoot0 hz0 hsp0 hspLe0 hspDisj0 hspLast0 hidx0 hdr0 hM0 hK0 hpre0 hstLe0 hrm0
      have hidx_lt : idx < L.length := by
        by_contra hge
        have hdn : L.drop idx = [] := List.drop_eq_nil_of_le (by omega)
        rw [hdn] at hdr0; cases hdr0
      have hent := hsp0.2 idx hidx_lt
      have hget : L[idx] = ⟨true, e, kept, fresh⟩ := by
        have h1 : L[idx] :: L.drop (idx + 1) = ⟨true, e, kept, fresh⟩ :: (rels' ++ spRest) := by
          rw [← List.drop_eq_getElem_cons hidx_lt, hdr0]; rfl
        exact (List.cons.inj h1).1
      have hdrop_next : L.drop (idx + 1) = rels' ++ spRest := by
        have h1 : L[idx] :: L.drop (idx + 1) = ⟨true, e, kept, fresh⟩ :: (rels' ++ spRest) := by
          rw [← List.drop_eq_getElem_cons hidx_lt, hdr0]; rfl
        exact (List.cons.inj h1).2
      have hcond1 : (Expr.reg 8).eval w st0 = some 1 := Expr.eval_reg_of_eq (by simpa using hr8)
      set entryPtr := spPtr + 1 + 4 * idx
      have he_mem : st0.mem (entryPtr + 1) = e := by rw [hent.2.1, hget]
      have hkept_mem : st0.mem (entryPtr + 2) = kept := by rw [hent.2.2.1, hget]
      have hfresh_mem : st0.mem (entryPtr + 3) = fresh := by rw [hent.2.2.2, hget]
      -- 4 entry-load assignments
      set rA := Function.update st0.regs 9 entryPtr
      set rB := Function.update rA 10 e
      set rC := Function.update rB 11 kept
      set rD := Function.update rC 12 fresh
      have ha9 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.reg 1) (.const 1))
          (.bin .mul (.const 4) (.reg 5)))) st0 .normal { st0 with regs := rA } 8 :=
        runs_assign_iff.mpr ⟨entryPtr,
          Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr5) (by omega)) (by omega),
          rfl, rfl, rfl⟩
      have ha10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const 1))))
          { st0 with regs := rA } .normal { st0 with regs := rB } 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA])) (Expr.eval_const (by omega)) (by omega))
          he_mem, rfl, rfl, rfl⟩
      have ha11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 9) (.const 2))))
          { st0 with regs := rB } .normal { st0 with regs := rC } 5 :=
        runs_assign_iff.mpr ⟨kept, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA])) (Expr.eval_const (by omega)) (by omega))
          hkept_mem, rfl, rfl, rfl⟩
      have ha12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 9) (.const 3))))
          { st0 with regs := rC } .normal { st0 with regs := rD } 5 :=
        runs_assign_iff.mpr ⟨fresh, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) (Expr.eval_const (by omega)) (by omega))
          hfresh_mem, rfl, rfl, rfl⟩
      -- Call `cut` + `outSmallSide` via `tourCut_and_smallSide_runs`
      have hrm_step : hC + tourSplitStepSpace eCap < 2 ^ w := by
        simp only [List.length_cons] at hrm0; rw [Nat.succ_mul] at hrm0; omega
      obtain ⟨bdCut, hbdCut, bdSS, hbdSS, o1, st1, c1, o2, st2, c2, tx2, Y,
        hrun1, hrun2, hrep2, hM2, hK2, hpre2, hpot2, ho1_lo, ho1_hi, ho2_lo, ho2_hi,
        hz2, hfr2, hft2, hcost12⟩ :=
        tourCut_and_smallSide_runs (pos := st0.pos) (extraAv := fun a => a < statePtr + 3)
          hpT hpO hw hrep0 hfoot0 (fun _ ha => by omega) hz0 hM0 hkM hME₀ hK0
          hpre0 he heM hkept_eq hfreshLt hfreshV hfreshNotR huniq' hSt hSh hrm_step
      set rE := Function.update rD 4 o1.value
      set rF := Function.update rE 13 o1.value
      set rG := Function.update rF 4 o2.value
      have heArgs1 : evalArgs w { st0 with regs := rD } [.reg 0, .reg 10, .reg 12, .reg 4] =
          some [tourH, e, fresh, hC] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, hr0])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rD, rC, rB])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rD])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, hr4])) <| evalArgs_nil _ _
      have hcall1 : Runs w p ω (.call 4 (tourOp bTour 1) [.reg 0, .reg 10, .reg 12, .reg 4])
          { st0 with regs := rD } .normal ⟨st1.mem, rE, st1.pos⟩
          (argsSize [.reg 0, .reg 10, .reg 12, .reg 4] + c1 + 1) :=
        runs_call_iff.mpr ⟨_, bdCut, o1, st1, c1, heArgs1, hbdCut, hrun1, rfl, rfl, rfl⟩
      have ha13 : Runs w p ω (.assign 13 (.reg 4)) ⟨st1.mem, rE, st1.pos⟩ .normal
          ⟨st1.mem, rF, st1.pos⟩ 2 :=
        runs_assign_iff.mpr ⟨o1.value, Expr.eval_reg_of_eq (by simp [rE]), rfl, rfl, rfl⟩
      have heArgs2 : evalArgs w ⟨st1.mem, rF, st1.pos⟩
          [.reg 0, .reg 11, .reg 12, .reg 11, .reg 12, .reg 7, .reg 13] =
          some [tourH, kept, fresh, kept, fresh, lst, o1.value] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC, rB, rA, hr0])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rF, rE, rD])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rF, rE, rD])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC, rB, rA, hr7])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rF])) <| evalArgs_nil _ _
      have hcall2 : Runs w p ω (.call 4 (outIdxSmallSide bOut)
          [.reg 0, .reg 11, .reg 12, .reg 11, .reg 12, .reg 7, .reg 13])
          ⟨st1.mem, rF, st1.pos⟩ .normal ⟨st2.mem, rG, st2.pos⟩
          (argsSize [.reg 0, .reg 11, .reg 12, .reg 11, .reg 12, .reg 7, .reg 13] + c2 + 1) :=
        runs_call_iff.mpr ⟨_, bdSS, o2, st2, c2, heArgs2, hbdSS, hrun2, rfl, rfl, rfl⟩
      -- Update `spP'`, `lst' = o1.value`, `idx' = idx + 1`, and check next `cont`
      set spP' := if spP = 0 then o1.value else spP
      set rH := Function.update rG 6 spP'
      have hcondSp : Runs w p ω (.cond (.bin .eq (.reg 6) (.const 0)) (.assign 6 (.reg 13)) .nop)
          ⟨st2.mem, rG, st2.pos⟩ .normal ⟨st2.mem, rH, st2.pos⟩
          (if spP = 0 then 6 else 5) := by
        by_cases h0 : spP = 0
        · have hev : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨st2.mem, rG, st2.pos⟩ = some 1 := by
            simp [Expr.eval, rG, rF, rE, rD, rC, rB, rA, hr6, h0, BinOp.eval,
              (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
          have ha6 : Runs w p ω (.assign 6 (.reg 13)) ⟨st2.mem, rG, st2.pos⟩ .normal
              ⟨st2.mem, rH, st2.pos⟩ 2 :=
            runs_assign_iff.mpr ⟨o1.value, Expr.eval_reg_of_eq (by simp [rG, rF]),
              rfl, by simp [rH, spP', h0], rfl⟩
          simpa [h0] using runs_cond_iff.mpr ⟨1, 2, hev, by simpa using ha6, rfl⟩
        · have hev : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨st2.mem, rG, st2.pos⟩ = some 0 := by
            simp [Expr.eval, rG, rF, rE, rD, rC, rB, rA, hr6, h0, BinOp.eval,
              (by omega : 0 < 2 ^ w)]
          have hrHeq : rH = rG := by
            funext r; by_cases hr : r = 6
            · subst hr; simp [rH, spP', h0, rG, rF, rE, rD, rC, rB, rA, hr6]
            · simp [rH, hr]
          have hnop : Runs w p ω .nop ⟨st2.mem, rG, st2.pos⟩ .normal ⟨st2.mem, rH, st2.pos⟩ 1 :=
            runs_nop_iff.mpr ⟨rfl, by rw [hrHeq], rfl⟩
          simpa [h0] using runs_cond_iff.mpr ⟨0, 1, hev, by simpa using hnop, rfl⟩
      set rI := Function.update rH 7 o1.value
      set rJ := Function.update rI 5 (idx + 1)
      have ha7 : Runs w p ω (.assign 7 (.reg 13)) ⟨st2.mem, rH, st2.pos⟩ .normal
          ⟨st2.mem, rI, st2.pos⟩ 2 :=
        runs_assign_iff.mpr ⟨o1.value, Expr.eval_reg_of_eq (by simp [rH, rG, rF]), rfl, rfl, rfl⟩
      have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 5) (.const 1))) ⟨st2.mem, rI, st2.pos⟩
          .normal ⟨st2.mem, rJ, st2.pos⟩ 4 :=
        runs_assign_iff.mpr ⟨idx + 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rI, rH, rG, rF, rE, rD, rC, rB, rA, hr5]))
            (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
      -- `SplitEntriesAt` is preserved at `st2.mem`
      have hsp_eq2 : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → st2.mem a = st0.mem a :=
        fun a ha1 ha2 => hfr2 a (by omega) (hspDisj0 a ha1 ha2)
          (by rcases hspLast0 with h0 | h1 | h2; exact Or.inl h0; exact Or.inr (by omega); exact Or.inr (by omega))
      have hsp2 : SplitEntriesAt st2.mem spPtr L := by
        refine ⟨(hsp_eq2 spPtr (le_refl _) (by omega)).trans hsp0.1, fun j hj => ?_⟩
        obtain ⟨e0, e1, e2, e3⟩ := hsp0.2 j hj
        exact ⟨(hsp_eq2 _ (by omega) (by omega)).trans e0, (hsp_eq2 _ (by omega) (by omega)).trans e1,
          (hsp_eq2 _ (by omega) (by omega)).trans e2, (hsp_eq2 _ (by omega) (by omega)).trans e3⟩
      have hrels'_t : ∀ r ∈ rels', r.isRelease = true := tourRelChain_all_true hrest
      obtain ⟨stN, cN, hrunN, hstN_mem, hstN_regs, hstN_r8, hcN⟩ :=
        consumeRel_check_runs hwide hsp_w hrest_stop ⟨st2.mem, rJ, st2.pos⟩ (idx + 1) rels'
          (by simp [rJ, rI, rH, rG, rF, rE, rD, rC, rB, rA, hr1])
          (by simp [rJ, rI, rH, rG, rF, rE, rD, rC, rB, rA, hr2])
          (by simp [rJ]) (by omega) hdrop_next hrels'_t hsp2
      -- Assemble body run and apply `ih`
      have hbody :=
        runs_seq_normal ha9 (runs_seq_normal ha10 (runs_seq_normal ha11 (runs_seq_normal ha12
          (runs_seq_normal hcall1 (runs_seq_normal ha13 (runs_seq_normal hcall2
            (runs_seq_normal hcondSp (runs_seq_normal ha7 (runs_seq_normal ha5 hrunN)))))))))
      have hfoot2 : ∀ a, (tourAsmRep vCap eCap).foot tourH tx2 a → a < o2.value := fun a ha => by
        rcases hft2 a ha with h0 | ⟨_, h2⟩
        · exact lt_of_lt_of_le (hfoot0 a h0) (by omega)
        · exact h2
      have hspDisj2 : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length →
          ¬ (tourAsmRep vCap eCap).foot tourH tx2 a := fun a ha1 ha2 hf2 => by
        rcases hft2 a hf2 with h0 | ⟨hge, _⟩
        · exact hspDisj0 a ha1 ha2 h0
        · omega
      have hrm_next : o2.value + rels'.length * tourSplitStepSpace eCap < 2 ^ w := by
        simp only [List.length_cons] at hrm0; rw [Nat.succ_mul] at hrm0; omega
      obtain ⟨hE, stF, cRest, txF, spF, lstF, YsRest, hrunRest, hr3F, hr4F, hr5F, hr6F, hr7F, hlstF,
        hrepF, hMF, hKF, hpreF, hpotF, hhLoF, hhHiF, hzF, hfrF, hftF, hcF⟩ :=
        ih (idx := idx + 1) (spP := spP') (lst := o1.value) (hC := o2.value)
          (st0 := stN) (tx0 := tx2) (Pd := Pd ++ [.split kept fresh (St ∩ keep) (Sh ∩ keep)])
          (Ysd := Ysd ++ [Y])
          (by rw [hstN_regs 0 (by decide)]; simp [rJ, rI, rH, rG, rF, rE, rD, rC, rB, rA, hr0])
          (by rw [hstN_regs 1 (by decide)]; simp [rJ, rI, rH, rG, rF, rE, rD, rC, rB, rA, hr1])
          (by rw [hstN_regs 2 (by decide)]; simp [rJ, rI, rH, rG, rF, rE, rD, rC, rB, rA, hr2])
          (by rw [hstN_regs 3 (by decide)]; simp [rJ, rI, rH, rG, rF, rE, rD, rC, rB, rA, hr3])
          (by rw [hstN_regs 4 (by decide)]; simp [rJ, rI, rH, rG])
          (by rw [hstN_regs 5 (by decide)]; simp [rJ])
          (by rw [hstN_regs 6 (by decide)]; simp [rJ, rI, rH])
          (by rw [hstN_regs 7 (by decide)]; simp [rJ, rI])
          hstN_r8 (by rw [hstN_mem]; exact hrep2) hfoot2 (by rw [hstN_mem]; exact hz2)
          (by rw [hstN_mem]; exact hsp2) (by omega) hspDisj2 (Or.inr (Or.inr (by omega)))
          (by omega) hdrop_next hM2 hK2 (by rw [hstN_mem]; exact hpre2) (by omega) hrm_next
      have hrunLoop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stN, _, _, hcond1, by decide, hbody, hrunRest, rfl⟩))
      refine ⟨hE, stF, _, txF, spF, lstF, Y :: YsRest, hrunLoop, hr3F, hr4F,
        by simp only [List.length_cons]; omega, hr6F, hr7F, Or.inr (by rcases hlstF with rfl | hge <;> omega),
        hrepF, hMF, hKF,
        by simpa only [List.append_assoc, List.singleton_append] using hpreF,
        ?_, by omega, by simp only [List.length_cons]; rw [Nat.succ_mul]; omega, hzF,
        fun a ha hnf hneL => by
          have hnf2 : ¬ (tourAsmRep vCap eCap).foot tourH tx2 a := fun hf2 => by
            rcases hft2 a hf2 with h0 | ⟨hge, _⟩; exact hnf h0; omega
          exact (hfrF a (by omega) hnf2 (Or.inr (by omega))).trans (by rw [hstN_mem]; exact hfr2 a ha hnf hneL),
        fun a ha => by
          rcases hftF a ha with h2 | ⟨hge, hlt⟩
          · rcases hft2 a h2 with h0 | ⟨hge2, hlt2⟩
            · exact Or.inl h0
            · exact Or.inr ⟨hge2, by omega⟩
          · exact Or.inr ⟨by omega, hlt⟩, ?_⟩
      · simp only [List.map_cons, List.sum_cons, MGraph.batchEnc, MGraph.updateEnc]
        clear * - hpot2 hpotF
        omega
      · simp only [List.map_cons, List.sum_cons, List.length_cons, argsSize, Expr.size] at hcF ⊢
        rw [hstN_mem] at hcF; dsimp only at hcF
        have hcStep : 1 + (8 + (5 + (5 + (5 + (4 + c1 + 1 + (2 + (7 + c2 + 1 +
            ((if spP = 0 then 6 else 5) + (2 + (4 + cN + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
            ≤ c1 + c2 + 120 := by clear * - hcN; split_ifs <;> omega
        have h120 : 120 ≤ 200 * (Y.length + 1) * ordStoreLog eCap :=
          le_trans (by omega) (Nat.le_mul_of_pos_right _ htl)
        have hstep_cost : (tourMul + outSmallSideMul * (tourOutSpec.mul + 1)) * (Y.length + 1) * ordStoreLog eCap +
            200 * (Y.length + 1) * ordStoreLog eCap =
            tourConsumeRelMul * (Y.length + 1) * ordStoreLog eCap := by
          dsimp only [tourConsumeRelMul]; rw [tourConsumeRelMulFn_eq, ← Nat.add_mul, ← Nat.add_mul]
        have htot_cost : tourConsumeRelMul * (Y.length + 1) * ordStoreLog eCap +
            tourConsumeRelMul * ((YsRest.map List.length).sum + rels'.length) * ordStoreLog eCap =
            tourConsumeRelMul * (Y.length + (YsRest.map List.length).sum + (rels'.length + 1)) *
              ordStoreLog eCap := by
          rw [← Nat.add_mul, ← Nat.mul_add,
            show Y.length + 1 + ((YsRest.map List.length).sum + rels'.length) =
              Y.length + (YsRest.map List.length).sum + (rels'.length + 1) by omega]
        clear * - hcost12 hcF hcStep h120 hstep_cost htot_cost
        omega

/-- **Verification of Helper 1 (`asmFirstTourConsumeRelStmt`)**: consumes all leading
`isRelease = true` entries described by `TourRelChain`. -/
theorem asmFirstTourConsumeRel_runs {w vCap eCap bTour bOut tourH spPtr statePtr hCur pos : ℕ}
    {p : Program} (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {s s_f : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    {L relL spRest : List CompSplitEntry} {spIdx splitPtr last : ℕ}
    {keep M E₀ : Finset ℕ} {G₀ S_cur S_f : MGraph} {P_done P_rel : List Update}
    {Ys_done : List (List End)}
    (hrep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < hCur) (hzero : ZeroFrom mem hCur)
    (hspAt : SplitEntriesAt mem spPtr L) (hsp_le : spPtr + 1 + 4 * L.length ≤ hCur)
    (hsp_disj : ∀ a, spPtr ≤ a → a < spPtr + 1 + 4 * L.length → ¬ (tourAsmRep vCap eCap).foot tourH tx a)
    (hst_mem : mem statePtr = spIdx ∧ mem (statePtr + 1) = splitPtr ∧ mem (statePtr + 2) = last)
    (hst_le : statePtr + 3 ≤ hCur)
    (hst_disj_foot : ∀ i < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx (statePtr + i))
    (_hst_disj_sp : statePtr + 3 ≤ spPtr ∨ spPtr + 1 + 4 * L.length ≤ statePtr)
    (_hst_disj_last : last = 0 ∨ last + 4 < statePtr ∨ statePtr + 3 ≤ last + 4)
    (hsp_disj_last : last = 0 ∨ last + 4 < spPtr ∨ spPtr + 1 + 4 * L.length ≤ last + 4)
    (hspIdx_le : spIdx ≤ L.length) (hdrop : L.drop spIdx = relL ++ spRest)
    (hrest_stop : ∀ e rest, spRest = e :: rest → e.isRelease = false)
    (hchain : TourRelChain vCap eCap keep M s S_cur relL P_rel s_f S_f)
    (hM : TourMarksAt s M) (hkM : keep ⊆ M) (hME₀ : M ⊆ E₀) (hK : TourKeepMatch keep s S_cur)
    (hpre : OutSplitPrefixAt mem splitPtr last hCur
      (fun a => (tourAsmRep vCap eCap).foot tourH tx a ∨ a < statePtr + 3)
      keep E₀ G₀ P_done S_cur Ys_done)
    (hroom : hCur + relL.length * tourSplitStepSpace eCap + 1 < 2 ^ w) :
    ∃ hEnd st' cost tx' splitPtr' last' Ys_rel,
      Runs w p ω (asmFirstTourConsumeRelStmt (tourOp bTour 1) (outIdxSmallSide bOut))
        (startState [tourH, spPtr, L.length, statePtr, hCur] mem pos) (.returned hEnd) st' cost ∧
      (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s_f) tx' st'.mem ∧
      TourMarksAt s_f M ∧ TourKeepMatch keep s_f S_f ∧
      st'.mem statePtr = spIdx + relL.length ∧ st'.mem (statePtr + 1) = splitPtr' ∧
      st'.mem (statePtr + 2) = last' ∧ (last' = last ∨ hCur ≤ last') ∧
      OutSplitPrefixAt st'.mem splitPtr' last' hEnd
        (fun a => (tourAsmRep vCap eCap).foot tourH tx' a ∨ a < statePtr + 3)
        keep E₀ G₀ (P_done ++ P_rel) S_f (Ys_done ++ Ys_rel) ∧
      (Ys_rel.map List.length).sum + tourMarkPot keep s_f ≤
        S_cur.batchEnc P_rel + tourMarkPot keep s ∧
      hCur ≤ hEnd ∧ hEnd ≤ hCur + relL.length * tourSplitStepSpace eCap ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a →
        (a < statePtr ∨ statePtr + 3 ≤ a) → (last = 0 ∨ a ≠ last + 4) → st'.mem a = mem a) ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH tx' a →
        (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < hEnd)) ∧
      cost + (tourAsmRep vCap eCap).phi tourH tx' st'.mem ≤
        tourConsumeRelMul * ((Ys_rel.map List.length).sum + relL.length + 1) * ordStoreLog eCap +
          (tourAsmRep vCap eCap).phi tourH tx mem := by
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  have hwide : 18 ≤ 2 ^ w :=
    (tourDS_wide_of_foot hrep hfoot (by omega : hCur + 1 < 2 ^ w)).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by omega)
  have hsp_w : spPtr + 1 + 4 * L.length < 2 ^ w := by omega
  -- Run the prologue of `asmFirstTourConsumeRelStmt`, invoke `consumeRel_loop_runs`, and epilogue
  set s0 := startState [tourH, spPtr, L.length, statePtr, hCur] mem pos
  set r5 := Function.update s0.regs 5 spIdx
  set r6 := Function.update r5 6 splitPtr
  set r7 := Function.update r6 7 last
  have ha5 : Runs w p ω (.assign 5 (.load (.reg 3))) s0 .normal ⟨mem, r5, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨spIdx, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [s0, startState]))
      hst_mem.1, rfl, rfl, rfl⟩
  have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 3) (.const 1)))) ⟨mem, r5, pos⟩
      .normal ⟨mem, r6, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨splitPtr, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5, s0, startState]))
        (Expr.eval_const (by omega)) (by omega)) hst_mem.2.1, rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 3) (.const 2)))) ⟨mem, r6, pos⟩
      .normal ⟨mem, r7, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨last, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r6, r5, s0, startState]))
        (Expr.eval_const (by omega)) (by omega)) hst_mem.2.2, rfl, rfl, rfl⟩
  have hrelL_t : ∀ r ∈ relL, r.isRelease = true := tourRelChain_all_true hchain
  obtain ⟨st1, c1, hrun1, hst1_mem, hst1_regs, hst1_r8, hc1⟩ :=
    consumeRel_check_runs hwide hsp_w hrest_stop ⟨mem, r7, pos⟩ spIdx relL
      (by simp [r7, r6, r5, s0, startState])
      (by simp [r7, r6, r5, s0, startState])
      (by simp [r7, r6, r5]) hspIdx_le hdrop hrelL_t hspAt
  obtain ⟨hE, stF, cL, txF, spF, lstF, YsR, hrunL, hr3F, hr4F, hr5F, hr6F, hr7F, hlstF,
    hrepF, hMF, hKF, hpreF, hpotF, hhLoF, hhHiF, hzF, hfrF, hftF, hcL⟩ :=
    consumeRel_loop_runs hpT hpO hw hwide htourW hsp_w hrest_stop hkM hME₀ hchain
      (idx := spIdx) (spP := splitPtr) (lst := last) (hC := hCur)
      (st0 := st1) (tx0 := tx) (Pd := P_done) (Ysd := Ys_done)
      (by rw [hst1_regs 0 (by decide)]; simp [r7, r6, r5, s0, startState])
      (by rw [hst1_regs 1 (by decide)]; simp [r7, r6, r5, s0, startState])
      (by rw [hst1_regs 2 (by decide)]; simp [r7, r6, r5, s0, startState])
      (by rw [hst1_regs 3 (by decide)]; simp [r7, r6, r5, s0, startState])
      (by rw [hst1_regs 4 (by decide)]; simp [r7, r6, r5, s0, startState])
      (by rw [hst1_regs 5 (by decide)]; simp [r7, r6, r5])
      (by rw [hst1_regs 6 (by decide)]; simp [r7, r6])
      (by rw [hst1_regs 7 (by decide)]; simp [r7])
      hst1_r8 (by rw [hst1_mem]; exact hrep) hfoot (by rw [hst1_mem]; exact hzero)
      (by rw [hst1_mem]; exact hspAt) hsp_le hsp_disj hsp_disj_last hspIdx_le hdrop hM hK
      (by rw [hst1_mem]; exact hpre) hst_le (by omega)
  -- Epilogue: store `[spIdx + relL.length, spF, lstF]` at `statePtr .. statePtr + 2` and return `hE`
  set m1 := Function.update stF.mem statePtr (spIdx + relL.length)
  set m2 := Function.update m1 (statePtr + 1) spF
  set m3 := Function.update m2 (statePtr + 2) lstF
  have hst0_w : Runs w p ω (.store (.reg 3) (.reg 5)) stF .normal { stF with mem := m1 } 3 :=
    runs_store_iff.mpr ⟨statePtr, spIdx + relL.length, Expr.eval_reg_of_eq hr3F,
      Expr.eval_reg_of_eq hr5F, rfl, rfl, rfl⟩
  have hst1_w : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 6))
      { stF with mem := m1 } .normal { stF with mem := m2 } 5 :=
    runs_store_iff.mpr ⟨statePtr + 1, spF,
      Expr.eval_add (Expr.eval_reg_of_eq hr3F) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq hr6F, rfl, rfl, rfl⟩
  have hst2_w : Runs w p ω (.store (.bin .add (.reg 3) (.const 2)) (.reg 7))
      { stF with mem := m2 } .normal { stF with mem := m3 } 5 :=
    runs_store_iff.mpr ⟨statePtr + 2, lstF,
      Expr.eval_add (Expr.eval_reg_of_eq hr3F) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq hr7F, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 4)) { stF with mem := m3 } (.returned hE)
      { stF with mem := m3 } 2 :=
    runs_ret_iff.mpr ⟨hE, Expr.eval_reg_of_eq hr4F, rfl, rfl, rfl⟩
  have hrun1_split : ∃ st1a c1a c1b,
      Runs w p ω (.assign 8 (.const 0)) ⟨mem, r7, pos⟩ .normal st1a c1a ∧
      Runs w p ω (.cond (.bin .lt (.reg 5) (.reg 2))
        (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 5)))))
        .nop) st1a .normal st1 c1b ∧ c1 = c1a + c1b + 1 := by
    rcases runs_seq_iff.mp hrun1 with ⟨_, _, _, hEq, _⟩ | ⟨st1a, c1a, c1b, hr1a, hr1b, hc1eq⟩
    · cases hEq
    · exact ⟨st1a, c1a, c1b, hr1a, hr1b, hc1eq⟩
  obtain ⟨st1a, c1a, c1b, hr1a, hr1b, hc1_eq⟩ := hrun1_split
  have hrunAll :=
    runs_seq_normal ha5 (runs_seq_normal ha6 (runs_seq_normal ha7
      (runs_seq_normal hr1a (runs_seq_normal hr1b (runs_seq_normal hrunL
        (runs_seq_normal hst0_w (runs_seq_normal hst1_w (runs_seq_normal hst2_w hret))))))))
  have hm3_out : ∀ a, (a < statePtr ∨ statePtr + 3 ≤ a) → m3 a = stF.mem a := fun a ha => by
    simp only [m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hfoot_disj_st : ∀ a, (tourAsmRep vCap eCap).foot tourH txF a → a < statePtr ∨ statePtr + 3 ≤ a :=
    fun a ha => by
      rcases hftF a ha with h0 | ⟨hge, _⟩
      · by_contra hnot; push Not at hnot
        exact hst_disj_foot (a - statePtr) (by omega) (by convert h0 using 1; omega)
      · exact Or.inr (by omega)
  have hlocF := tourAsmRep_local vCap eCap tourH (tourToAsmTour s_f) txF stF.mem m3 fun a ha =>
    (hm3_out a (hfoot_disj_st a ha)).symm
  have hpreM3 := outSplitPrefixAt_mono hpreF (le_refl _) (fun _ _ hna => hna)
    (fun a _ hna => hm3_out a (by
      by_contra hnot; push Not at hnot
      exact hna (Or.inr (by omega))))
  refine ⟨hE, { stF with mem := m3 }, _, txF, spF, lstF, YsR, hrunAll, hlocF.1 hrepF, hMF, hKF,
    by simp [m3, m2, m1], by simp [m3, m2], by simp [m3], hlstF, hpreM3, hpotF, hhLoF, hhHiF,
    fun a ha => (hm3_out a (Or.inr (by omega))).trans (hzF a ha),
    fun a ha hnf hst hnl => (hm3_out a hst).trans ((hfrF a ha hnf hnl).trans (by rw [hst1_mem])),
    hftF, ?_⟩
  rw [← hlocF.2]
  have h100 : 100 ≤ tourConsumeRelMul * ordStoreLog eCap :=
    le_trans (by dsimp only [tourConsumeRelMul]; rw [tourConsumeRelMulFn_eq]; omega) (Nat.le_mul_of_pos_right _ htl)
  have hdist : tourConsumeRelMul * ((YsR.map List.length).sum + relL.length + 1) * ordStoreLog eCap =
      tourConsumeRelMul * ((YsR.map List.length).sum + relL.length) * ordStoreLog eCap +
        tourConsumeRelMul * ordStoreLog eCap := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
  rw [hst1_mem] at hcL
  dsimp only at hcL
  clear * - hc1 hc1_eq hcL h100 hdist
  omega

end

end MinCostFlow.SparseCore.Program
