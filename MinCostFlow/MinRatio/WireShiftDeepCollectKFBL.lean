module

public import MinCostFlow.MinRatio.WireShiftDeepSteps
public import MinCostFlow.MinRatio.WireCoreReadKFBL
import WordRAM.Tactic

/-!
# The forest collection loop of the deep shift under the layout contract

The deep shift reads the active forests of the levels `first, …, d - 1` twice: before the rebuild
(the old forests) and after it (the new forests). The loop `collectLSFForestsLoop` does this with
op `2` of the sparse-core module. This file proves `collectLSFForestsLoopKFBL_runs`, the `KFBL`
copy of `collectLSFForestsLoop_runs` (`WireShiftDeepPhases.lean`).

The `K` theorem asks the caller where each forest lies (`hForestRead`). Under
`SparseCoreReadoutFootAt` op `2` puts the forest below the heap and in the footprint of the core
(`ordCoreReadLSFKFBL_runs`). So this theorem proves that the graph of the forest of level `j`
lies in the final footprint of core `j`. The caller gets the rest from the disjointness of the
cores. `shiftDeepCollectNewKFBL_runs` is the `KFBL` copy of `shiftDeepCollectNew_runs`
(`WireShiftDeepRestart.lean`), the collection of the new forests in Phase 4.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

section PhaseRuns

/-- The invariant of `collectLSFForestsLoopKFBL_runs` before level `cur`. -/
private structure CollectLSFInvKFBL {w L first baseIdx dstReg dstPtrs handleBase branchBase
    levelMeta : ℕ} {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (chain : ChainState T CP)
    (coreHandle : ℕ → ℕ) (tok0 : ℕ → Rcore.τ) (st0 : State)
    (cur : ℕ) (s : State) (pot : ℕ) : Prop where
  r19 : s.regs 19 = cur
  r20 : s.regs 20 = first
  r71 : s.regs 71 = baseIdx
  r75 : s.regs 75 = CP.d
  r77 : s.regs 77 = handleBase
  r78 : s.regs 78 = branchBase
  r83 : s.regs 83 = levelMeta
  rDst : s.regs dstReg = dstPtrs
  rKeep : ∀ r, (70 ≤ r) ∨ r = 20 ∨ r = 21 → s.regs r = st0.regs r
  hLo : st0.regs 4 ≤ s.regs 4
  hHi : s.regs 4 ≤ st0.regs 4 + 5 * (cur - first)
  hz : ZeroFrom s.mem (s.regs 4)
  toks : ∃ tok : ℕ → Rcore.τ,
    (∀ j, first ≤ j → j < CP.d →
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (tok j) s.mem ∧
      (j < cur → ∀ a, Rcore.foot (coreHandle j) (tok j) a →
        Rcore.foot (coreHandle j) (tok0 j) a ∨ (st0.regs 4 ≤ a ∧ a < s.regs 4)) ∧
      (cur ≤ j → tok j = tok0 j)) ∧
    (∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (tok j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (tok j₂) a) ∧
    (∀ j, first ≤ j → j < cur →
      ∃ vc ec,
        DynGraphAt s.mem (s.mem (dstPtrs + (j - baseIdx))) vc ec
          (T.lsfs (chain.scState j) (chain.bran j)).F.F ∧
        s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec ≤ s.regs 4 ∧
        (∀ a, s.mem (dstPtrs + (j - baseIdx)) ≤ a →
          a < s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec →
          Rcore.foot (coreHandle j) (tok j) a)) ∧
    pot = (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (tok j) s.mem)
  frame : ∀ a < st0.regs 4,
    (∀ j, first ≤ j → j < cur → ¬ Rcore.foot (coreHandle j) (tok0 j) a) →
    (a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (cur - baseIdx) ≤ a) →
    s.mem a = st0.mem a

/-- **The forest collection loop under the layout contract.** `collectLSFForestsLoop` reads, for
each level `j` in `[first, d)`, the active forest with op `2` and stores its graph pointer at
`dstPtrs + (j - baseIdx)`. It keeps every core and their disjointness, and its cost is
`(d - first) * (P.readout + 48) + 7` plus the change of the potentials. The graph of the forest
of level `j` lies in the footprint of core `j`, since op `2` puts it below the heap. -/
theorem collectLSFForestsLoopKFBL_runs
    {w L depth vCap eCap capExp first baseIdx dstReg dstPtrs handleBase branchBase
      levelMeta : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (chain : ChainState T CP) (coreHandle : ℕ → ℕ) (coreTok0 : ℕ → Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hDstReg : 70 ≤ dstReg)
    (hBaseLe : baseIdx ≤ first) (hFirstLe : first ≤ CP.d)
    (h20 : st.regs 20 = first) (h71 : st.regs 71 = baseIdx) (h75 : st.regs 75 = CP.d)
    (h77 : st.regs 77 = handleBase) (h78 : st.regs 78 = branchBase)
    (h83 : st.regs 83 = levelMeta) (hDst : st.regs dstReg = dstPtrs)
    (hkW : CP.k < 2 ^ w) (hdW : CP.d < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hMetaEnd : levelMeta + 2 * CP.d ≤ st.regs 4) (hHEnd : handleBase + CP.d ≤ st.regs 4)
    (hBEnd : branchBase + CP.d ≤ st.regs 4)
    (hDstEnd : dstPtrs + (CP.d - baseIdx) ≤ st.regs 4)
    (hRoom : st.regs 4 + 5 * (CP.d - first) < 2 ^ w)
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hFootAt : ∀ j, first ≤ j → j < CP.d →
      SparseCoreReadoutFootAt fmt L depth T (chain.G j) CP.k (chain.lvlM j) chain.N₀ vCap eCap
        capExp P allocation Rcore p op)
    (hCores : ∀ j, first ≤ j → j < CP.d →
      st.mem (handleBase + j) = coreHandle j ∧
      st.mem (branchBase + j) = chain.bran j ∧
      chain.bran j < CP.k ∧ coreHandle j < 2 ^ w ∧
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok0 j) st.mem ∧
      SparseCoreOrdInput T CP.k (chain.lvlM j) chain.N₀ (chain.scState j) (chain.G j)
        (chain.levelOrd j) (chain.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → a < st.regs 4) ∧
      (∀ r, first ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (levelMeta + CP.d + j)) ∧
      (handleBase + j < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ handleBase + j) ∧
      (branchBase + j < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ branchBase + j) ∧
      (levelMeta + CP.d + j < dstPtrs + (first - baseIdx) ∨
        dstPtrs + (CP.d - baseIdx) ≤ levelMeta + CP.d + j) ∧
      (∀ t, first - baseIdx ≤ t → t < CP.d - baseIdx →
        ¬ Rcore.foot (coreHandle j) (coreTok0 j) (dstPtrs + t)) ∧
      (DynGraphAt st.mem (st.mem (levelMeta + CP.d + j)) vCap eCap (chain.G j) ∧
        st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap ≤ st.regs 4 ∧
        (∀ a, st.mem (levelMeta + CP.d + j) ≤ a →
          a < st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap →
          (∀ r, first ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
          (a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ a))))
    (hCoreDisj : ∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (coreTok0 j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (coreTok0 j₂) a) :
    ∃ (out : State) (c : ℕ) (coreTok' : ℕ → Rcore.τ),
      Runs w p ω (collectLSFForestsLoop (op 2) dstReg) st .normal out c ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 5 * (CP.d - first) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ j, first ≤ j → j < CP.d →
        Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok' j) out.mem ∧
        (∀ a, Rcore.foot (coreHandle j) (coreTok' j) a →
          Rcore.foot (coreHandle j) (coreTok0 j) a ∨ (st.regs 4 ≤ a ∧ a < out.regs 4))) ∧
      (∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (coreHandle j₁) (coreTok' j₁) a →
          ¬ Rcore.foot (coreHandle j₂) (coreTok' j₂) a) ∧
      (∀ j, first ≤ j → j < CP.d →
        ∃ vc ec,
          DynGraphAt out.mem (out.mem (dstPtrs + (j - baseIdx))) vc ec
            (T.lsfs (chain.scState j) (chain.bran j)).F.F ∧
          out.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec ≤ out.regs 4 ∧
          (∀ a, out.mem (dstPtrs + (j - baseIdx)) ≤ a →
            a < out.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec →
            Rcore.foot (coreHandle j) (coreTok' j) a)) ∧
      (∀ a < st.regs 4,
        (∀ j, first ≤ j → j < CP.d → ¬ Rcore.foot (coreHandle j) (coreTok0 j) a) →
        (a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, (70 ≤ r) ∨ r = 20 ∨ r = 21 → out.regs r = st.regs r) ∧
      c + (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) out.mem) ≤
        (CP.d - first) * (P.readout + 48) + 7 +
        (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) := by
  let Inv := CollectLSFInvKFBL (w := w) (L := L) (first := first) (baseIdx := baseIdx)
    (dstReg := dstReg) (dstPtrs := dstPtrs) (handleBase := handleBase)
    (branchBase := branchBase) (levelMeta := levelMeta) (fmt := fmt) Rcore chain coreHandle
    coreTok0 st
  let pot0 := (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem)
  have hInv0 : Inv first { st with regs := Function.update st.regs 19 first } pot0 :=
    { r19 := by simp, r20 := by simp [h20], r71 := by simp [h71], r75 := by simp [h75],
      r77 := by simp [h77], r78 := by simp [h78], r83 := by simp [h83],
      rDst := by simp [Function.update_of_ne (by omega : dstReg ≠ 19), hDst],
      rKeep := fun r hr => Function.update_of_ne (by omega) _ _,
      hLo := le_rfl, hHi := by simp, hz := hz0,
      toks := ⟨coreTok0, fun j hj1 hj2 => ⟨(hCores j hj1 hj2).2.2.2.2.1, fun h => by omega, fun _ => rfl⟩,
        hCoreDisj, fun _ h1 h2 => by omega, rfl⟩,
      frame := fun _ _ _ _ => rfl }
  -- Note `forRange 19 (.reg 20) (.reg 75)` has upper bound `.reg 75` (not `.reg 21`),
  -- so we prove the loop by direct induction on `rem = CP.d - cur` mirroring `forRange19_runs_with_pot`.
  have hwne0 : w ≠ 0 := by intro h; subst h; omega
  let body : Stmt :=
    .assign 3 (.load (.bin .add (.reg 77) (.reg 19))) ;;
    .assign 2 (.load (.bin .add (.reg 78) (.reg 19))) ;;
    .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 19))) ;;
    ordCoreReadLSFStmt (op 2) ;;
    .store (.bin .add (.reg dstReg) (.bin .sub (.reg 19) (.reg 71)))
      (.load (.bin .add (.reg 4) (.const 1))) ;;
    .assign 4 (.reg 5)
  let sInit := { st with regs := Function.update st.regs 19 first }
  have rInit : Runs w p ω (.assign 19 (.reg 20)) st .normal sInit 2 :=
    runs_assign_iff.mpr ⟨first, by simp [Expr.eval, h20], rfl, rfl, rfl⟩
  suffices hUp : ∀ (rem cur : ℕ) (s : State) (pot : ℕ),
      first ≤ cur → cur + rem = CP.d → Inv cur s pot →
      ∃ out c potEnd,
        Runs w p ω (forUp 19 (.reg 75) body) s .normal out c ∧
        Inv CP.d out potEnd ∧
        c + potEnd ≤ rem * (P.readout + 48) + pot + 4 by
    obtain ⟨out, c, potEnd, rLoop, hEnd, hc⟩ := hUp (CP.d - first) first sInit pot0 le_rfl (by omega) hInv0
    obtain ⟨tokEnd, hTokRep, hTokDisj, hForests, hPotEq⟩ := hEnd.toks
    refine ⟨out, 2 + c + 1, tokEnd, runs_seq_iff.mpr (Or.inr ⟨sInit, 2, c, rInit, rLoop, rfl⟩),
      hEnd.hLo, hEnd.hHi, hEnd.hz,
      fun j hj1 hj2 => ⟨(hTokRep j hj1 hj2).1, (hTokRep j hj1 hj2).2.1 hj2⟩,
      hTokDisj,
      hForests,
      hEnd.frame, hEnd.rKeep, by rw [← hPotEq]; omega⟩
  intro rem
  induction rem with
  | zero =>
    intro cur s pot hge hsum hInv
    have hcur : cur = CP.d := by omega
    subst hcur
    refine ⟨s, 4, pot, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hInv.r19, hInv.r75],
      rfl, rfl, by simp [Expr.size]⟩), hInv, by simp; omega⟩
  | succ rem ih =>
    intro cur s pot hge hsum hInv
    have hlt : cur < CP.d := by omega
    obtain ⟨tok, hTokRep, hTokDisj, hForests, hPotEq⟩ := hInv.toks
    obtain ⟨hHCell, hBCell, hBrLt, hChW, _, hInCur, hFoot0Cur, hNotCell, hHOutD, hBOutD,
      hMOutD, hDstNotF, hDG0, hDGEnd0, hDGDisj0⟩ := hCores cur hge hlt
    have hTokCurEq : tok cur = coreTok0 cur := (hTokRep cur hge hlt).2.2 le_rfl
    have hHCellS : s.mem (handleBase + cur) = coreHandle cur :=
      (hInv.frame _ (by omega) (fun r hr1 hr2 => (hNotCell r hr1 (by omega)).1)
        (by rcases hHOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hHCell
    have hBCellS : s.mem (branchBase + cur) = chain.bran cur :=
      (hInv.frame _ (by omega) (fun r hr1 hr2 => (hNotCell r hr1 (by omega)).2.1)
        (by rcases hBOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hBCell
    have hGPtrS : s.mem (levelMeta + CP.d + cur) = st.mem (levelMeta + CP.d + cur) :=
      hInv.frame _ (by omega) (fun r hr1 hr2 => (hNotCell r hr1 (by omega)).2.2)
        (by rcases hMOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
    have hDGS : DynGraphAt s.mem (st.mem (levelMeta + CP.d + cur)) vCap eCap (chain.G cur) :=
      dynGraphAt_of_agree hDG0 (fun a ha1 ha2 => by
        obtain ⟨hNF, hOutD⟩ := hDGDisj0 a ha1 ha2
        exact hInv.frame a (by omega) (fun r hr1 hr2 => hNF r hr1 (by omega))
          (by rcases hOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
    let s1 := { s with regs := Function.update s.regs 3 (coreHandle cur) }
    let s2 := { s1 with regs := Function.update s1.regs 2 (chain.bran cur) }
    let s3 := { s2 with regs := Function.update s2.regs 6 (st.mem (levelMeta + CP.d + cur)) }
    have r1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 19)))) s .normal s1 5 :=
      runs_assign_iff.mpr ⟨coreHandle cur, by simp [Expr.eval, BinOp.eval, hInv.r77, hInv.r19,
        show handleBase + cur < 2 ^ w by omega, hHCellS], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 19)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨chain.bran cur, by simp [Expr.eval, BinOp.eval, s1, hInv.r78, hInv.r19,
        show branchBase + cur < 2 ^ w by omega, hBCellS], rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 19))))
        s2 .normal s3 7 :=
      runs_assign_iff.mpr ⟨st.mem (levelMeta + CP.d + cur), by simp [Expr.eval, BinOp.eval, s2, s1,
        hInv.r83, hInv.r75, hInv.r19, show levelMeta + CP.d < 2 ^ w by omega,
        show levelMeta + CP.d + cur < 2 ^ w by omega, hGPtrS], rfl, rfl, rfl⟩
    have hFootCurS : ∀ a, Rcore.foot (coreHandle cur) (tok cur) a → a < s.regs 4 := fun a ha =>
      (hFoot0Cur a (hTokCurEq ▸ ha)).trans_le hInv.hLo
    obtain ⟨s4, ret4, c4, y4, r4, hs4_5, hrep4, _, ⟨vcF, ecF, hLSF4, hFEnd4, hFIn4⟩, _, _, _,
        hresp4, hc4, hs4_regs⟩ :=
      ordCoreReadLSFKFBL_runs (ω := ω) (st := s3) (hFootAt cur hge hlt)
        (by simp [s3, s2]) (by simp [s3, s2, s1]) (by simp [s3]) (by simp [s3, s2, s1])
        hBrLt hkW hChW hDGS (hDGEnd0.trans hInv.hLo) (hTokRep cur hge hlt).1 hInCur hFootCurS
        hInv.hz (by have := hInv.hHi; omega)
    have hretLo : s.regs 4 ≤ ret4 := hresp4.1
    have hretHi : ret4 ≤ s.regs 4 + 5 := hresp4.2.1
    let dstCell := dstPtrs + (cur - baseIdx)
    let fPtr := s4.mem (s.regs 4 + 1)
    let s5 := { s4 with mem := Function.update s4.mem dstCell fPtr }
    let s6 := { s5 with regs := Function.update s5.regs 4 ret4 }
    have hs4_r (r : ℕ) (hr : r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 6) : s4.regs r = s.regs r := by
      rw [hs4_regs r hr.2.2.1]
      simp [s3, s2, s1, Function.update_of_ne hr.2.2.2, Function.update_of_ne hr.1,
        Function.update_of_ne hr.2.1]
    have hs4_1W : s.regs 4 + 1 < 2 ^ w := by have := hInv.hHi; omega
    have r5 : Runs w p ω (.store (.bin .add (.reg dstReg) (.bin .sub (.reg 19) (.reg 71)))
        (.load (.bin .add (.reg 4) (.const 1)))) s4 .normal s5 10 :=
      runs_store_iff.mpr ⟨dstCell, fPtr,
        by simp [Expr.eval, BinOp.eval, hs4_r dstReg (by omega), hs4_r 19 (by omega),
          hs4_r 71 (by omega), hInv.rDst, hInv.r19, hInv.r71, dstCell,
          show cur - baseIdx < 2 ^ w by omega,
          show dstPtrs + (cur - baseIdx) < 2 ^ w by omega],
        by simp [Expr.eval, BinOp.eval, hs4_r 4 (by omega), hw1, hs4_1W, fPtr],
        rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 4 (.reg 5)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨ret4, by simp [Expr.eval, s5, hs4_5], rfl, rfl, rfl⟩
    have rBody : Runs w p ω body s .normal s6 (5 + (5 + (7 + (c4 + (10 + 2 + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 10, 2, r5, r6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    -- Update tokens and potential
    let tok' : ℕ → Rcore.τ := fun j => if j = cur then y4 else tok j
    have hDstNotFootCur : ¬ Rcore.foot (coreHandle cur) y4 dstCell := by
      intro hf
      rcases hresp4.2.2.2.2 dstCell hf with h0 | ⟨hlo, _⟩
      · exact hDstNotF (cur - baseIdx) (by omega) (by omega) (hTokCurEq ▸ h0)
      · have := hInv.hLo; omega
    have hlocY4 := hCoreLocal (coreHandle cur) (chainLevelOrdAbs chain cur) y4 s4.mem s6.mem
      (fun a ha => by
        have hne : a ≠ dstCell := fun h => hDstNotFootCur (h ▸ ha)
        simp [s6, s5, Function.update_of_ne hne])
    have hOtherPres (j : ℕ) (hj1 : first ≤ j) (hj2 : j < CP.d) (hne : j ≠ cur) :
        Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (tok j) s6.mem ∧
        Rcore.phi (coreHandle j) (tok j) s6.mem = Rcore.phi (coreHandle j) (tok j) s.mem := by
      have hlocJ := hCoreLocal (coreHandle j) (chainLevelOrdAbs chain j) (tok j) s.mem s6.mem
        (fun a ha => by
          have hnfCur : ¬ Rcore.foot (coreHandle cur) (tok cur) a := fun hc =>
            hTokDisj cur j hge hlt hj1 hj2 hne.symm a hc ha
          have haLt : a < s.regs 4 := by
            by_cases hjlt : j < cur
            · rcases (hTokRep j hj1 hj2).2.1 hjlt a ha with h0 | ⟨_, hhi⟩
              · exact ((hCores j hj1 hj2).2.2.2.2.2.2.1 a h0).trans_le hInv.hLo
              · exact hhi
            · have hjeq := (hTokRep j hj1 hj2).2.2 (by omega)
              exact ((hCores j hj1 hj2).2.2.2.2.2.2.1 a (hjeq ▸ ha)).trans_le hInv.hLo
          have hneDst : a ≠ dstCell := by
            intro heq; subst heq
            by_cases hjlt : j < cur
            · rcases (hTokRep j hj1 hj2).2.1 hjlt dstCell ha with h0 | ⟨hlo, _⟩
              · exact (hCores j hj1 hj2).2.2.2.2.2.2.2.2.2.2.2.1 (cur - baseIdx) (by omega) (by omega) h0
              · omega
            · have hjeq := (hTokRep j hj1 hj2).2.2 (by omega)
              exact (hCores j hj1 hj2).2.2.2.2.2.2.2.2.2.2.2.1 (cur - baseIdx) (by omega) (by omega)
                (hjeq ▸ ha)
          change s.mem a = Function.update s4.mem dstCell fPtr a
          rw [Function.update_of_ne hneDst, hresp4.2.2.2.1 a haLt hnfCur])
      exact ⟨hlocJ.1 (hTokRep j hj1 hj2).1, hlocJ.2.symm⟩
    let pot' := (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (tok' j) s6.mem)
    have hPotDiff :
        pot' + Rcore.phi (coreHandle cur) (tok cur) s.mem =
          pot + Rcore.phi (coreHandle cur) y4 s4.mem := by
      have hMem : cur ∈ Finset.Ico first CP.d := Finset.mem_Ico.mpr ⟨hge, hlt⟩
      have hS1 := Finset.add_sum_erase (Finset.Ico first CP.d)
        (fun j => Rcore.phi (coreHandle j) (tok' j) s6.mem) hMem
      have hS2 := Finset.add_sum_erase (Finset.Ico first CP.d)
        (fun j => Rcore.phi (coreHandle j) (tok j) s.mem) hMem
      have hEraseEq :
          (Finset.Ico first CP.d |>.erase cur).sum (fun j => Rcore.phi (coreHandle j) (tok' j) s6.mem) =
          (Finset.Ico first CP.d |>.erase cur).sum (fun j => Rcore.phi (coreHandle j) (tok j) s.mem) :=
        Finset.sum_congr rfl (fun j hj => by
          obtain ⟨hne, hmem'⟩ := Finset.mem_erase.mp hj
          obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hmem'
          simp only [tok', hne, ↓reduceIte]
          exact (hOtherPres j hj1 hj2 hne).2)
      have hCurEq : Rcore.phi (coreHandle cur) (tok' cur) s6.mem =
          Rcore.phi (coreHandle cur) y4 s4.mem := by
        simp only [tok', ↓reduceIte]; exact hlocY4.2.symm
      dsimp only [pot']; rw [hPotEq, ← hS1, ← hS2, hCurEq, hEraseEq]; omega
    -- Build `Inv (cur + 1)` on `s7`
    let s7 := { s6 with regs := Function.update s6.regs 19 (cur + 1) }
    have hs7_r (r : ℕ) (h19 : r ≠ 19) (h4 : r ≠ 4) (h2 : r ≠ 2) (h3 : r ≠ 3) (h5 : r ≠ 5) (h6 : r ≠ 6) :
        s7.regs r = s.regs r := by
      simp only [s7, s6, s5, Function.update_of_ne h19, Function.update_of_ne h4]
      exact hs4_r r ⟨h2, h3, h5, h6⟩
    have hFootF : ∀ a, fPtr ≤ a → a < fPtr + dynGraphSize vcF ecF →
        Rcore.foot (coreHandle cur) y4 a := fun a ha1 ha2 =>
      (hFIn4 a ha1 ha2).resolve_right (fun h => by have := h.1; dsimp only [fPtr] at ha2; omega)
    have hInvNext : Inv (cur + 1) s7 pot' :=
      { r19 := by simp [s7],
        r20 := (hs7_r 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r20,
        r71 := (hs7_r 71 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r71,
        r75 := (hs7_r 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r75,
        r77 := (hs7_r 77 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r77,
        r78 := (hs7_r 78 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r78,
        r83 := (hs7_r 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r83,
        rDst := (hs7_r dstReg (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hInv.rDst,
        rKeep := fun r hr =>
          (hs7_r r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hInv.rKeep r hr),
        hLo := by simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]; exact hInv.hLo.trans hretLo,
        hHi := by simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]; have := hInv.hHi; omega,
        hz := fun a ha => by
          simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self] at ha
          have hne : a ≠ dstCell := by have := hInv.hLo; omega
          simp only [s7, s6, s5, Function.update_of_ne hne]
          exact hresp4.2.2.1 a ha,
        toks := ⟨tok',
          fun j hj1 hj2 => by
            by_cases hjeq : j = cur
            · subst hjeq
              simp only [s7, tok', ↓reduceIte]
              refine ⟨hlocY4.1 hrep4, fun _ a ha => ?_, fun h => by omega⟩
              simp only [s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]
              rcases hresp4.2.2.2.2 a ha with h0 | ⟨hlo, hhi⟩
              · exact Or.inl (hTokCurEq ▸ h0)
              · exact Or.inr ⟨hInv.hLo.trans hlo, hhi⟩
            · simp only [s7, tok', hjeq, ↓reduceIte]
              refine ⟨(hOtherPres j hj1 hj2 hjeq).1, fun hjlt a ha => ?_,
                fun hjge => (hTokRep j hj1 hj2).2.2 (by omega)⟩
              simp only [s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]
              rcases (hTokRep j hj1 hj2).2.1 (by omega) a ha with h0 | ⟨hlo, hhi⟩
              · exact Or.inl h0
              · exact Or.inr ⟨hlo, hhi.trans_le hretLo⟩,
          fun j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2 => by
            by_cases e1 : j₁ = cur <;> by_cases e2 : j₂ = cur
            · exact hne (e1.trans e2.symm)
            · subst e1; simp only [tok', ↓reduceIte, e2] at ha1 ha2
              rcases hresp4.2.2.2.2 a ha1 with h0 | ⟨hlo, _⟩
              · exact hTokDisj j₁ j₂ h1 h2 h3 h4 hne a h0 ha2
              · by_cases hj2lt : j₂ < j₁
                · rcases (hTokRep j₂ h3 h4).2.1 hj2lt a ha2 with h0' | ⟨_, hhi'⟩
                  · have := (hCores j₂ h3 h4).2.2.2.2.2.2.1 a h0'; have := hInv.hLo; omega
                  · omega
                · have hjeq := (hTokRep j₂ h3 h4).2.2 (by omega)
                  have := (hCores j₂ h3 h4).2.2.2.2.2.2.1 a (hjeq ▸ ha2); have := hInv.hLo; omega
            · subst e2; simp only [tok', ↓reduceIte, e1] at ha1 ha2
              rcases hresp4.2.2.2.2 a ha2 with h0 | ⟨hlo, _⟩
              · exact hTokDisj j₁ j₂ h1 h2 h3 h4 hne a ha1 h0
              · by_cases hj1lt : j₁ < j₂
                · rcases (hTokRep j₁ h1 h2).2.1 hj1lt a ha1 with h0' | ⟨_, hhi'⟩
                  · have := (hCores j₁ h1 h2).2.2.2.2.2.2.1 a h0'; have := hInv.hLo; omega
                  · omega
                · have hjeq := (hTokRep j₁ h1 h2).2.2 (by omega)
                  have := (hCores j₁ h1 h2).2.2.2.2.2.2.1 a (hjeq ▸ ha1); have := hInv.hLo; omega
            · simp only [tok', e1, e2, ↓reduceIte] at ha1 ha2
              exact hTokDisj j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2,
          fun j hj1 hj2 => by
            by_cases hjeq : j = cur
            · subst hjeq
              have hDstEq : s7.mem (dstPtrs + (j - baseIdx)) = fPtr := by simp [s7, s6, s5, dstCell]
              refine ⟨vcF, ecF, ?_, ?_, ?_⟩
              · rw [hDstEq]
                exact dynGraphAt_of_agree hLSF4.2.1 (fun a ha1 ha2 => by
                  have hne : a ≠ dstCell := fun h => hDstNotFootCur (h ▸ hFootF a ha1 ha2)
                  simp [s7, s6, s5, Function.update_of_ne hne])
              · rw [hDstEq]
                simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19),
                  Function.update_self]
                exact hFEnd4.trans hretLo
              · rw [hDstEq]; simp only [tok', ↓reduceIte]; exact hFootF
            · obtain ⟨vcJ, ecJ, hDGJ, hEndJ, hFootJ⟩ := hForests j hj1 (by omega)
              have hNotCurJ : ∀ a, s.mem (dstPtrs + (j - baseIdx)) ≤ a →
                  a < s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vcJ ecJ →
                  ¬ Rcore.foot (coreHandle cur) (tok cur) a := fun a ha1 ha2 hf =>
                hTokDisj j cur hj1 (by omega) hge hlt hjeq a (hFootJ a ha1 ha2) hf
              have hNotDstJ : ∀ a, s.mem (dstPtrs + (j - baseIdx)) ≤ a →
                  a < s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vcJ ecJ → a ≠ dstCell :=
                fun a ha1 ha2 heq => by
                  have hf := hFootJ a ha1 ha2
                  rw [heq] at hf
                  rcases (hTokRep j hj1 (by omega)).2.1 (by omega) dstCell hf with h0 | ⟨hlo, _⟩
                  · exact (hCores j hj1 (by omega)).2.2.2.2.2.2.2.2.2.2.2.1 (cur - baseIdx) (by omega)
                      (by omega) h0
                  · dsimp [dstCell] at hlo; omega
              have hCellNe : dstPtrs + (j - baseIdx) ≠ dstCell := by dsimp [dstCell]; omega
              have hPtrEq : s7.mem (dstPtrs + (j - baseIdx)) = s.mem (dstPtrs + (j - baseIdx)) := by
                simp only [s7, s6, s5, Function.update_of_ne hCellNe]
                exact hresp4.2.2.2.1 _ (by have := hInv.hLo; omega)
                  (fun hf => hDstNotF (j - baseIdx) (by omega) (by omega) (hTokCurEq ▸ hf))
              refine ⟨vcJ, ecJ, ?_, by
                  rw [hPtrEq]
                  simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19),
                    Function.update_self]
                  exact hEndJ.trans hretLo,
                fun a ha1 ha2 => by
                  simp only [tok', hjeq, ↓reduceIte]
                  exact hFootJ a (hPtrEq ▸ ha1) (hPtrEq ▸ ha2)⟩
              rw [hPtrEq]
              exact dynGraphAt_of_agree hDGJ (fun a ha1 ha2 => by
                simp only [s7, s6, s5, Function.update_of_ne (hNotDstJ a ha1 ha2)]
                exact hresp4.2.2.2.1 a (by omega) (hNotCurJ a ha1 ha2))
          , rfl⟩,
        frame := fun a ha hNF hOutD => by
          have hneDst : a ≠ dstCell := by dsimp [dstCell]; omega
          simp only [s7, s6, s5, Function.update_of_ne hneDst]
          rw [hresp4.2.2.2.1 a (ha.trans_le hInv.hLo) (fun hf => hNF cur hge (Nat.lt_succ_self cur) (hTokCurEq ▸ hf))]
          exact hInv.frame a ha (fun r hr1 hr2 => hNF r hr1 (by omega))
            (by rcases hOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]) }
    have rInc : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.const 1))) s6 .normal s7 4 :=
      runs_assign_iff.mpr ⟨cur + 1, by simp [Expr.eval, BinOp.eval, s6, s5, hs4_r 19 (by omega),
        hInv.r19, hw1, show cur + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    obtain ⟨out, cRest, potEnd, rRest, hInvEnd, hcRest⟩ := ih (cur + 1) s7 pot' (by omega) (by omega) hInvNext
    have rAll : Runs w p ω (forUp 19 (.reg 75) body) s .normal out
        (((5 + (5 + (7 + (c4 + (10 + 2 + 1) + 1) + 1) + 1) + 1) + 4 + 1) + cRest + 4) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s7, _, cRest,
        by simp [Expr.eval, BinOp.eval, hInv.r19, hInv.r75, hlt, hwne0],
        by omega,
        runs_seq_iff.mpr (Or.inr ⟨s6, _, 4, rBody, rInc, rfl⟩),
        rRest, by simp [Expr.size]; omega⟩))
    refine ⟨out, _, potEnd, rAll, hInvEnd, ?_⟩
    have hmul : (rem + 1) * (P.readout + 48) = rem * (P.readout + 48) + (P.readout + 48) := by ring
    change c4 + Rcore.phi (coreHandle cur) y4 s4.mem ≤ P.readout + 5 + Rcore.phi (coreHandle cur) (tok cur) s.mem at hc4
    omega

end PhaseRuns

/-- **The new-forest collection of Phase 4 under the layout contract.** The program
`.assign 20 (.reg 71) ;; collectLSFForestsLoop (op 2) 81 ;; collectTermForestStmt 81` collects the
active forests of `next` on `[i0, d]` into `newPtrs` (`reg 81`). It gives
`ForestPtrListAt out.mem newPtrs (chainSuffixForests next i0) intCap (out.regs 4)`, keeps the cores
on `[i0, d)` and telescopes their potentials. It is the `KFBL` copy of
`shiftDeepCollectNew_runs`: the place of each forest comes from `collectLSFForestsLoopKFBL_runs`,
so only the edge bound `hIntCap` of the forests is asked. -/
theorem shiftDeepCollectNewKFBL_runs
    {w L depth vCap eCap capExp i0 handleBase branchBase levelMeta newPtrs intCap termHandle
      vcLast ecLast lsfHdr forestPtr : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (next : ChainState T CP) (coreHandle : ℕ → ℕ) (coreTok0 : ℕ → Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hiLt : i0 < CP.d)
    (h71 : st.regs 71 = i0) (h75 : st.regs 75 = CP.d)
    (h77 : st.regs 77 = handleBase) (h78 : st.regs 78 = branchBase)
    (h81 : st.regs 81 = newPtrs) (h83 : st.regs 83 = levelMeta)
    (hkW : CP.k < 2 ^ w) (hdW : CP.d < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hMetaEnd : levelMeta + 2 * CP.d ≤ st.regs 4) (hHEnd : handleBase + CP.d + 1 ≤ st.regs 4)
    (hBEnd : branchBase + CP.d + 1 ≤ st.regs 4)
    (hNewEnd : newPtrs + (CP.d - i0 + 1) ≤ st.regs 4)
    (hRoom : st.regs 4 + 5 * (CP.d - i0) < 2 ^ w)
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hFootAt : ∀ j, i0 ≤ j → j < CP.d →
      SparseCoreReadoutFootAt fmt L depth T (next.G j) CP.k (next.lvlM j) next.N₀ vCap eCap
        capExp P allocation Rcore p op)
    (hCores : ∀ j, i0 ≤ j → j < CP.d →
      st.mem (handleBase + j) = coreHandle j ∧
      st.mem (branchBase + j) = next.bran j ∧
      next.bran j < CP.k ∧ coreHandle j < 2 ^ w ∧
      Rcore.rep (coreHandle j) (chainLevelOrdAbs next j) (coreTok0 j) st.mem ∧
      SparseCoreOrdInput T CP.k (next.lvlM j) next.N₀ (next.scState j) (next.G j)
        (next.levelOrd j) (next.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → a < st.regs 4) ∧
      (∀ r, i0 ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (levelMeta + CP.d + j)) ∧
      (handleBase + j < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ handleBase + j) ∧
      (branchBase + j < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ branchBase + j) ∧
      (levelMeta + CP.d + j < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ levelMeta + CP.d + j) ∧
      (∀ t < CP.d - i0 + 1, ¬ Rcore.foot (coreHandle j) (coreTok0 j) (newPtrs + t)) ∧
      (DynGraphAt st.mem (st.mem (levelMeta + CP.d + j)) vCap eCap (next.G j) ∧
        st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap ≤ st.regs 4 ∧
        (∀ a, st.mem (levelMeta + CP.d + j) ≤ a →
          a < st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap →
          (∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
          (a < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ a))))
    (hCoreDisj : ∀ j₁ j₂, i0 ≤ j₁ → j₁ < CP.d → i0 ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (coreTok0 j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (coreTok0 j₂) a)
    (hTermH : st.mem (handleBase + CP.d) = termHandle)
    (hTermB : st.mem (branchBase + CP.d) = next.lastBran)
    (hTermLsf : st.mem (termHandle + 1 + next.lastBran) = lsfHdr)
    (hTermFPtr : st.mem (lsfHdr + 1) = forestPtr)
    (hTermFDG : DynGraphAt st.mem forestPtr vcLast ecLast (next.lastLSFs next.lastBran).F.F)
    (hTermFEnd : forestPtr + dynGraphSize vcLast ecLast ≤ st.regs 4)
    (hTermFCap : ∀ e ∈ (next.lastLSFs next.lastBran).F.F.E, e < intCap)
    (hTermDisjCells :
      (handleBase + CP.d < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ handleBase + CP.d) ∧
      (branchBase + CP.d < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ branchBase + CP.d) ∧
      (termHandle + 1 + next.lastBran < newPtrs ∨
        newPtrs + (CP.d - i0 + 1) ≤ termHandle + 1 + next.lastBran) ∧
      (lsfHdr + 1 < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ lsfHdr + 1) ∧
      termHandle + 1 + next.lastBran < st.regs 4 ∧ lsfHdr + 1 < st.regs 4 ∧
      (∀ r, i0 ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + CP.d) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + CP.d) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (termHandle + 1 + next.lastBran) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (lsfHdr + 1)) ∧
      (∀ a, forestPtr ≤ a → a < forestPtr + dynGraphSize vcLast ecLast →
        (∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
        (a < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ a)))
    (hIntCap : ∀ j, i0 ≤ j → j < CP.d →
      ∀ e ∈ (T.lsfs (next.scState j) (next.bran j)).F.F.E, e < intCap) :
    ∃ (out : State) (c : ℕ) (coreTok' : ℕ → Rcore.τ),
      Runs w p ω
        (.assign 20 (.reg 71) ;; collectLSFForestsLoop (op 2) 81 ;; collectTermForestStmt 81)
        st .normal out c ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 5 * (CP.d - i0) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      ForestPtrListAt out.mem newPtrs (chainSuffixForests next i0) intCap (out.regs 4) ∧
      (∀ j, i0 ≤ j → j < CP.d →
        Rcore.rep (coreHandle j) (chainLevelOrdAbs next j) (coreTok' j) out.mem ∧
        (∀ a, Rcore.foot (coreHandle j) (coreTok' j) a →
          Rcore.foot (coreHandle j) (coreTok0 j) a ∨ (st.regs 4 ≤ a ∧ a < out.regs 4))) ∧
      (∀ j₁ j₂, i0 ≤ j₁ → j₁ < CP.d → i0 ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (coreHandle j₁) (coreTok' j₁) a →
          ¬ Rcore.foot (coreHandle j₂) (coreTok' j₂) a) ∧
      (∀ a < st.regs 4,
        (∀ j, i0 ≤ j → j < CP.d → ¬ Rcore.foot (coreHandle j) (coreTok0 j) a) →
        (a < newPtrs ∨ newPtrs + (CP.d - i0 + 1) ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      c + (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) out.mem) ≤
        (CP.d - i0) * (P.readout + 48) + 50 +
        (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) := by
  let s1 := { st with regs := Function.update st.regs 20 i0 }
  have r1 : Runs w p ω (.assign 20 (.reg 71)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨i0, by simp [Expr.eval, h71], rfl, rfl, rfl⟩
  obtain ⟨s2, cLoop, coreTok', rLoop, hs2_lo, hs2_hi, hz2, hTokRep2, hTokDisj2, hForests2,
      hs2_fr, hs2_regs, hcLoop⟩ :=
    collectLSFForestsLoopKFBL_runs (w := w) (L := L) (capExp := capExp)
      (first := i0) (baseIdx := i0) (dstReg := 81) (dstPtrs := newPtrs)
      (handleBase := handleBase) (branchBase := branchBase) (levelMeta := levelMeta)
      (p := p) (ω := ω) (st := s1) next coreHandle coreTok0 hCoreLocal (by decide)
      le_rfl (le_of_lt hiLt) (by simp [s1]) (by simp [s1, h71]) (by simp [s1, h75])
      (by simp [s1, h77]) (by simp [s1, h78]) (by simp [s1, h83]) (by simp [s1, h81])
      hkW hdW hw1 hMetaEnd (by simp [s1]; omega) (by simp [s1]; omega) (by simp [s1]; omega) (by simpa [s1] using hRoom)
      hz0 hFootAt
      (fun j hj1 hj2 => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hG, hE, hD⟩ :=
          hCores j hj1 hj2
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8,
          by rcases h9 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
          by rcases h10 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
          by rcases h11 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
          fun t _ ht2 => h12 t (by omega),
          hG, hE, fun a ha1 ha2 => ⟨(hD a ha1 ha2).1,
            by rcases (hD a ha1 ha2).2 with h | h <;>
              [exact Or.inl (by omega); exact Or.inr (by omega)]⟩⟩)
      hCoreDisj
  obtain ⟨hTHO, hTBO, hTLO, hTFO, hTLLt, hTFLt, hTNf, hTFDisj⟩ := hTermDisjCells
  have hs2_eq (a : ℕ) (ha : a < st.regs 4) (hnf : ∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a)
      (hout : a < newPtrs ∨ newPtrs + (CP.d - i0) ≤ a) : s2.mem a = st.mem a :=
    hs2_fr a ha hnf (by rcases hout with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
  obtain ⟨out, cTerm, rTerm, hcTerm, houtMem, houtRegs⟩ :=
    collectTermForestStmt_runs (w := w) (dstReg := 81) (dstPtrs := newPtrs) (baseIdx := i0)
      (d := CP.d) (handleBase := handleBase) (branchBase := branchBase) (termHandle := termHandle)
      (lastBran := next.lastBran) (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (p := p) (ω := ω) (st := s2)
      ((hs2_regs 81 (Or.inl (by decide))).trans (by simp [s1, h81]))
      ((hs2_regs 71 (Or.inl (by decide))).trans (by simp [s1, h71]))
      ((hs2_regs 75 (Or.inl (by decide))).trans (by simp [s1, h75]))
      ((hs2_regs 77 (Or.inl (by decide))).trans (by simp [s1, h77]))
      ((hs2_regs 78 (Or.inl (by decide))).trans (by simp [s1, h78]))
      (by decide) (le_of_lt hiLt)
      ((hs2_eq _ (by omega) (fun r hr1 hr2 => (hTNf r hr1 hr2).1)
        (by rcases hTHO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermH)
      ((hs2_eq _ (by omega) (fun r hr1 hr2 => (hTNf r hr1 hr2).2.1)
        (by rcases hTBO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermB)
      ((hs2_eq _ hTLLt (fun r hr1 hr2 => (hTNf r hr1 hr2).2.2.1)
        (by rcases hTLO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermLsf)
      ((hs2_eq _ hTFLt (fun r hr1 hr2 => (hTNf r hr1 hr2).2.2.2)
        (by rcases hTFO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermFPtr)
      (by omega) (by omega) (by omega) (by omega) (by omega) hw1
  have hout4 : out.regs 4 = s2.regs 4 := houtRegs 4 (by decide) (by decide) (by decide)
  have hs1_4 : s1.regs 4 = st.regs 4 := rfl
  have hs1_m : s1.mem = st.mem := rfl
  rw [hs1_4] at hs2_lo hs2_hi
  rw [hs1_m] at hcLoop
  have hCorePres (j : ℕ) (hj1 : i0 ≤ j) (hj2 : j < CP.d) :
      Rcore.rep (coreHandle j) (chainLevelOrdAbs next j) (coreTok' j) out.mem ∧
      Rcore.phi (coreHandle j) (coreTok' j) out.mem =
        Rcore.phi (coreHandle j) (coreTok' j) s2.mem := by
    have hloc := hCoreLocal (coreHandle j) (chainLevelOrdAbs next j) (coreTok' j) s2.mem out.mem
      (fun a ha => by
        have hne : a ≠ newPtrs + (CP.d - i0) := by
          rcases (hTokRep2 j hj1 hj2).2 a ha with h0 | ⟨hlo, _⟩
          · exact fun heq => (hCores j hj1 hj2).2.2.2.2.2.2.2.2.2.2.2.1 (CP.d - i0) (by omega) (heq ▸ h0)
          · omega
        rw [houtMem, Function.update_of_ne hne])
    exact ⟨hloc.1 (hTokRep2 j hj1 hj2).1, hloc.2.symm⟩
  have hForestList : ForestPtrListAt out.mem newPtrs (chainSuffixForests next i0) intCap (out.regs 4) := by
    rw [hout4]
    refine ⟨by rw [chainSuffixForests_length]; omega, fun t ht => ?_⟩
    rw [chainSuffixForests_length] at ht
    by_cases htLt : t < CP.d - i0
    · rw [chainSuffixForests_getElem_lt next htLt]
      obtain ⟨vcT, ecT, hDGT, hEndT, hFootT⟩ := hForests2 (i0 + t) (by omega) (by omega)
      have hSub : i0 + t - i0 = t := by omega
      rw [hSub] at hDGT hEndT hFootT
      have hOutT : ∀ a, s2.mem (newPtrs + t) ≤ a →
          a < s2.mem (newPtrs + t) + dynGraphSize vcT ecT → a ≠ newPtrs + (CP.d - i0) :=
        fun a ha1 ha2 heq => by
          have hf := hFootT a ha1 ha2
          rw [heq] at hf
          rcases (hTokRep2 (i0 + t) (by omega) (by omega)).2 _ hf with h0 | ⟨hlo, _⟩
          · exact (hCores (i0 + t) (by omega) (by omega)).2.2.2.2.2.2.2.2.2.2.2.1 (CP.d - i0)
              (by omega) h0
          · omega
      have hPtrT : out.mem (newPtrs + t) = s2.mem (newPtrs + t) := by
        rw [houtMem, Function.update_of_ne (by omega)]
      refine ⟨vcT, ecT, ?_, hPtrT.symm ▸ hEndT, hIntCap (i0 + t) (by omega) (by omega)⟩
      rw [hPtrT]
      exact dynGraphAt_of_agree hDGT (fun a ha1 ha2 => by
        rw [houtMem, Function.update_of_ne (hOutT a ha1 ha2)])
    · have htEq : t = CP.d - i0 := by omega
      subst htEq
      rw [chainSuffixForests_getElem_last]
      have hPtrL : out.mem (newPtrs + (CP.d - i0)) = forestPtr := by rw [houtMem, Function.update_self]
      refine ⟨vcLast, ecLast, ?_, hPtrL.symm ▸ (hTermFEnd.trans hs2_lo), hTermFCap⟩
      rw [hPtrL]
      exact dynGraphAt_of_agree hTermFDG (fun a ha1 ha2 => by
        obtain ⟨hNF, hOut⟩ := hTFDisj a ha1 ha2
        rw [houtMem, Function.update_of_ne (by rcases hOut with h | h <;> omega)]
        exact hs2_eq a (by omega) hNF (by rcases hOut with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
  have hPhiEq :
      (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) out.mem) =
      (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) s2.mem) :=
    Finset.sum_congr rfl (fun j hj => (hCorePres j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2).2)
  refine ⟨out, 2 + (cLoop + cTerm + 1) + 1, coreTok',
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, cLoop + cTerm + 1, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, cLoop, cTerm, rLoop, rTerm, rfl⟩), rfl⟩),
    hout4.symm ▸ hs2_lo, hout4.symm ▸ hs2_hi,
    fun a ha => by
      rw [hout4] at ha; rw [houtMem, Function.update_of_ne (by omega : a ≠ newPtrs + (CP.d - i0))]
      exact hz2 a ha,
    hForestList,
    fun j hj1 hj2 => ⟨(hCorePres j hj1 hj2).1, fun a ha => hout4.symm ▸ (hTokRep2 j hj1 hj2).2 a ha⟩,
    hTokDisj2,
    fun a ha hnf hout => by
      rw [houtMem, Function.update_of_ne (by rcases hout with h | h <;> omega)]
      exact hs2_eq a ha hnf (by rcases hout with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]),
    fun r hr => (houtRegs r (by omega) (by omega) (by omega)).trans
      ((hs2_regs r (Or.inl hr)).trans (by simp [s1, Function.update_of_ne (by omega : r ≠ 20)])),
    by rw [hPhiEq]; omega⟩

end MinCostFlow.MinRatio
