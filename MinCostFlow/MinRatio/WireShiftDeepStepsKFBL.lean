module

public import MinCostFlow.MinRatio.WireShiftDeepCollectKFBL
public import MinCostFlow.MinRatio.WireCoreForestCapKFBL
public import MinCostFlow.MinRatio.GraphLiveCopy
import WordRAM.Tactic

/-!
# Phase 1 of the deep shift under the layout contract (`WireShiftDeepStepsKFBL`)

Phase 1 of the deep shift (`shiftDeepCollectOldKFBL`) keeps the old active forests of the levels
`i, …, d` before the shift changes them. It copies the forest of level `i` to fresh memory using
`copyGraphLiveFromHeader` (`GraphLiveCopy.lean`) in `O(Fi0.n + Fi0.m + 1)` time instead of scanning
the full capacity arrays, reads the forests of the levels `i + 1, …, d - 1` with op `2`, and adds
the forest of the last level `d`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

/-- Phase 1 under `sparseCoreOrdMachineContractKFBL`: identical to `shiftDeepCollectOld`, except
that level `i`'s old forest is copied into fresh zero memory by `copyGraphLiveFromHeader` in
`O(Fi0.n + Fi0.m + 1)` time. -/
@[expose] def shiftDeepCollectOldKFBL (readLSF : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 77) (.reg 71))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 71))) ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 71))) ;;
  ordCoreReadLSFStmt readLSF ;;
  .assign 6 (.load (.bin .add (.reg 4) (.const 1))) ;;
  .assign 4 (.reg 5) ;;
  copyGraphLiveFromHeader ;;
  .store (.reg 80) (.reg 6) ;;
  .assign 4 (.reg 5) ;;
  .assign 20 (.bin .add (.reg 71) (.const 1)) ;;
  collectLSFForestsLoop readLSF 80 ;;
  collectTermForestStmt 80

theorem shiftDeepCollectOldKFBL_noRand (readLSF : ℕ) :
    (shiftDeepCollectOldKFBL readLSF).NoRand := by
  simp [shiftDeepCollectOldKFBL, ordCoreReadLSFStmt_noRand, copyGraphLiveFromHeader_noRand,
    collectLSFForestsLoop_noRand, collectTermForestStmt_noRand, Stmt.NoRand]

set_option maxHeartbeats 400000 in
/-- **Phase 1 of the deep shift under the layout contract.** `shiftDeepCollectOldKFBL` copies the
old active forest of level `i0` to fresh memory in `copyGraphLiveCost` steps, collects the forests
of the levels `i0 + 1, …, d - 1`, and adds the forest of the last level `d`. It gives
`ForestPtrListAt out.mem oldPtrs (chainSuffixForests chain i0) intCap (out.regs 4)`, and every
forest of the list avoids the new footprint of core `i0` and meets `forestSafe`. -/
theorem shiftDeepCollectOldKFBL_runs
    {w L depth vCap eCap capExp fcap i0 handleBase branchBase levelMeta oldPtrs intCap termHandle
      vcLast ecLast lsfHdr forestPtr : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (chain : ChainState T CP) (coreHandle : ℕ → ℕ) (coreTok0 : ℕ → Rcore.τ)
    (forestSafe : ℕ → Prop)
    (hSafeAbove : ∀ a, st.regs 4 ≤ a → forestSafe a)
    (hSafeCore : ∀ j, i0 < j → j < CP.d → ∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a →
      forestSafe a)
    (hCoreLocal : Rcore.Local)
    (hiLt : i0 < CP.d)
    (h71 : st.regs 71 = i0) (h75 : st.regs 75 = CP.d)
    (h77 : st.regs 77 = handleBase) (h78 : st.regs 78 = branchBase)
    (h80 : st.regs 80 = oldPtrs) (h83 : st.regs 83 = levelMeta)
    (hkW : CP.k < 2 ^ w) (hdW : CP.d < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hMetaEnd : levelMeta + 2 * CP.d ≤ st.regs 4) (hHEnd : handleBase + CP.d + 1 ≤ st.regs 4)
    (hBEnd : branchBase + CP.d + 1 ≤ st.regs 4)
    (hOldEnd : oldPtrs + (CP.d - i0 + 1) ≤ st.regs 4)
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hFootAt : ∀ j, i0 ≤ j → j < CP.d →
      SparseCoreReadoutFootAt fmt L depth T (chain.G j) CP.k (chain.lvlM j) chain.N₀ vCap eCap
        capExp P allocation Rcore p op)
    (hForestCap : SparseCoreForestCapAt fmt L depth T (chain.G i0) CP.k (chain.lvlM i0) chain.N₀
      vCap eCap capExp P allocation fcap Rcore p op)
    (hCores : ∀ j, i0 ≤ j → j < CP.d →
      st.mem (handleBase + j) = coreHandle j ∧
      st.mem (branchBase + j) = chain.bran j ∧
      chain.bran j < CP.k ∧ coreHandle j < 2 ^ w ∧
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok0 j) st.mem ∧
      SparseCoreOrdInput T CP.k (chain.lvlM j) chain.N₀ (chain.scState j) (chain.G j)
        (chain.levelOrd j) (chain.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → a < st.regs 4) ∧
      (∀ r, i0 ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (levelMeta + CP.d + j)) ∧
      (handleBase + j < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ handleBase + j) ∧
      (branchBase + j < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ branchBase + j) ∧
      (levelMeta + CP.d + j < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ levelMeta + CP.d + j) ∧
      (∀ t < CP.d - i0 + 1, ¬ Rcore.foot (coreHandle j) (coreTok0 j) (oldPtrs + t)) ∧
      (DynGraphAt st.mem (st.mem (levelMeta + CP.d + j)) vCap eCap (chain.G j) ∧
        st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap ≤ st.regs 4 ∧
        (∀ a, st.mem (levelMeta + CP.d + j) ≤ a →
          a < st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap →
          (∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
          (a < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ a))))
    (hCoreDisj : ∀ j₁ j₂, i0 ≤ j₁ → j₁ < CP.d → i0 ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (coreTok0 j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (coreTok0 j₂) a)
    -- Terminal level `d` active forest hypotheses
    (hTermH : st.mem (handleBase + CP.d) = termHandle)
    (hTermB : st.mem (branchBase + CP.d) = chain.lastBran)
    (hTermLsf : st.mem (termHandle + 1 + chain.lastBran) = lsfHdr)
    (hTermFPtr : st.mem (lsfHdr + 1) = forestPtr)
    (hTermFDG : DynGraphAt st.mem forestPtr vcLast ecLast (chain.lastLSFs chain.lastBran).F.F)
    (hTermFEnd : forestPtr + dynGraphSize vcLast ecLast ≤ st.regs 4)
    (hTermFCap : ∀ e ∈ (chain.lastLSFs chain.lastBran).F.F.E, e < intCap)
    (hTermDisjCells :
      (handleBase + CP.d < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ handleBase + CP.d) ∧
      (branchBase + CP.d < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ branchBase + CP.d) ∧
      (termHandle + 1 + chain.lastBran < oldPtrs ∨
        oldPtrs + (CP.d - i0 + 1) ≤ termHandle + 1 + chain.lastBran) ∧
      (lsfHdr + 1 < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ lsfHdr + 1) ∧
      termHandle + 1 + chain.lastBran < st.regs 4 ∧ lsfHdr + 1 < st.regs 4 ∧
      (∀ r, i0 ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + CP.d) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + CP.d) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (termHandle + 1 + chain.lastBran) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (lsfHdr + 1)) ∧
      (∀ a, forestPtr ≤ a → a < forestPtr + dynGraphSize vcLast ecLast →
        (∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
        (a < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ a) ∧ forestSafe a))
    (hRoom : st.regs 4 + 5 + fcap + 5 * (CP.d - (i0 + 1)) < 2 ^ w)
    (hIntCap : ∀ j, i0 ≤ j → j < CP.d →
      ∀ e ∈ (T.lsfs (chain.scState j) (chain.bran j)).F.F.E, e < intCap) :
    ∃ (out : State) (c vcFi0 ecFi0 : ℕ) (yI0 : Rcore.τ),
      Runs w p ω (shiftDeepCollectOldKFBL (op 2)) st .normal out c ∧
      st.regs 4 ≤ out.regs 4 ∧
      out.regs 4 ≤ st.regs 4 + 5 + dynGraphSize vcFi0 ecFi0 + 5 * (CP.d - (i0 + 1)) ∧
      dynGraphSize vcFi0 ecFi0 ≤ fcap ∧
      ZeroFrom out.mem (out.regs 4) ∧
      DynGraphAt out.mem (out.mem oldPtrs) vcFi0 ecFi0 (T.lsfs (chain.scState i0) (chain.bran i0)).F.F ∧
      st.regs 4 ≤ out.mem oldPtrs ∧
      (∀ a, out.mem oldPtrs ≤ a → a < out.mem oldPtrs + dynGraphSize vcFi0 ecFi0 →
        ¬ Rcore.foot (coreHandle i0) yI0 a) ∧
      ForestPtrListAt out.mem oldPtrs (chainSuffixForests chain i0) intCap (out.regs 4) ∧
      (∀ t (ht : t < (chainSuffixForests chain i0).length),
        ∃ vc ec,
          DynGraphAt out.mem (out.mem (oldPtrs + t)) vc ec (chainSuffixForests chain i0)[t] ∧
          out.mem (oldPtrs + t) + dynGraphSize vc ec ≤ out.regs 4 ∧
          (∀ e ∈ (chainSuffixForests chain i0)[t].E, e < intCap) ∧
          (∀ a, out.mem (oldPtrs + t) ≤ a → a < out.mem (oldPtrs + t) + dynGraphSize vc ec →
            ¬ Rcore.foot (coreHandle i0) yI0 a ∧ forestSafe a)) ∧
      Rcore.rep (coreHandle i0) (chainLevelOrdAbs chain i0) yI0 out.mem ∧
      (∀ a, Rcore.foot (coreHandle i0) yI0 a →
        Rcore.foot (coreHandle i0) (coreTok0 i0) a ∨ (st.regs 4 ≤ a ∧ a < out.regs 4)) ∧
      (∀ a < st.regs 4,
        (∀ j, i0 ≤ j → j < CP.d → ¬ Rcore.foot (coreHandle j) (coreTok0 j) a) →
        (a < oldPtrs ∨ oldPtrs + (CP.d - i0 + 1) ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      c + Rcore.phi (coreHandle i0) yI0 out.mem ≤
        copyGraphLiveCost (T.lsfs (chain.scState i0) (chain.bran i0)).F.F.n
          (T.lsfs (chain.scState i0) (chain.bran i0)).F.F.m +
        (CP.d - i0) * (P.readout + 48) + 120 +
        (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) := by
  -- Step 1: level `i0` op `2` + `copyGraphFromHeader`
  obtain ⟨hH0, hB0, hBrLt0, hChW0, hRep0, hIn0, hFoot0, hNotCell0, hHOut0, hBOut0, hMOut0,
    hOldNotF0, hDG0, hDGEnd0, hDGDisj0⟩ := hCores i0 le_rfl hiLt
  let s1 := { st with regs := Function.update st.regs 3 (coreHandle i0) }
  let s2 := { s1 with regs := Function.update s1.regs 2 (chain.bran i0) }
  let s3 := { s2 with regs := Function.update s2.regs 6 (st.mem (levelMeta + CP.d + i0)) }
  have r1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 71)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨coreHandle i0, by simp [Expr.eval, BinOp.eval, h77, h71,
      show handleBase + i0 < 2 ^ w by omega, hH0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 71)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨chain.bran i0, by simp [Expr.eval, BinOp.eval, s1, h78, h71,
      show branchBase + i0 < 2 ^ w by omega, hB0], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 71))))
      s2 .normal s3 7 :=
    runs_assign_iff.mpr ⟨st.mem (levelMeta + CP.d + i0), by simp [Expr.eval, BinOp.eval, s2, s1,
      h83, h75, h71, show levelMeta + CP.d < 2 ^ w by omega,
      show levelMeta + CP.d + i0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨s4, ret4, c4, y4, r4, hs4_5, hrep4, _, ⟨vcFi0, ecFi0, hLSF4, hFEnd4, _, hFcap4⟩,
      hresp4, hc4, hs4_regs⟩ :=
    ordCoreReadLSFKFBLCap_runs (ω := ω) (st := s3) hForestCap
      (by simp [s3, s2]) (by simp [s3, s2, s1]) (by simp [s3]) (by simp [s3, s2, s1])
      hBrLt0 hkW hChW0 hDG0 hDGEnd0 hRep0 hIn0 hFoot0 hz0 (by omega)
  have hret4Lo : st.regs 4 ≤ ret4 := hresp4.1
  have hret4Hi : ret4 ≤ st.regs 4 + 5 := hresp4.2.1
  have hFi0End : s4.mem (st.regs 4 + 1) + dynGraphSize vcFi0 ecFi0 ≤ ret4 := hFEnd4.trans hret4Lo
  have hFi0Cap : ∀ e ∈ (T.lsfs (chain.scState i0) (chain.bran i0)).F.F.E, e < intCap :=
    hIntCap i0 le_rfl hiLt
  have hs4_r (r : ℕ) (hr : r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 6) : s4.regs r = st.regs r := by
    rw [hs4_regs r hr.2.2.1]
    simp [s3, s2, s1, Function.update_of_ne hr.2.2.2, Function.update_of_ne hr.1,
      Function.update_of_ne hr.2.1]
  let rawFi0 := s4.mem (st.regs 4 + 1)
  let s5 := { s4 with regs := Function.update s4.regs 6 rawFi0 }
  let s6 := { s5 with regs := Function.update s5.regs 4 ret4 }
  have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 4) (.const 1)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨rawFi0, by simp [Expr.eval, BinOp.eval, hs4_r 4 (by omega),
      show 1 < 2 ^ w by omega, show st.regs 4 + 1 < 2 ^ w by omega, rawFi0], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 4 (.reg 5)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨ret4, by simp [Expr.eval, s5, hs4_5], rfl, rfl, rfl⟩
  obtain ⟨s7, cCopy, r7, hCopyDG, hs7_6, hs7_5, hz7, hs7_fr, _, hcCopy, hs7_regs⟩ :=
    copyGraphLiveFromHeader_runs (p := p) (ω := ω) (st := s6) (by simp [s6, s5, rawFi0])
      (by simp [s6, s5, hs4_5]) hLSF4.2.1 hFi0End (by omega) hw9 hresp4.2.2.1
  let hCopyEnd := ret4 + dynGraphSize vcFi0 ecFi0
  let s8 := { s7 with mem := Function.update s7.mem oldPtrs ret4 }
  let s9 := { s8 with regs := Function.update s8.regs 4 hCopyEnd }
  let s10 := { s9 with regs := Function.update s9.regs 20 (i0 + 1) }
  have hs7_high (r : ℕ) (hr : 70 ≤ r) : s7.regs r = st.regs r := by
    rw [hs7_regs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
    simp only [s6, s5, Function.update_of_ne (by omega : r ≠ 4), Function.update_of_ne (by omega : r ≠ 6)]
    exact hs4_r r (by omega)
  have r8 : Runs w p ω (.store (.reg 80) (.reg 6)) s7 .normal s8 3 :=
    runs_store_iff.mpr ⟨oldPtrs, ret4, by simp [Expr.eval, hs7_high 80 (by decide), h80],
      by simp [Expr.eval, hs7_6], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 4 (.reg 5)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨hCopyEnd, by simp [Expr.eval, s8, hs7_5, hCopyEnd], rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 20 (.bin .add (.reg 71) (.const 1))) s9 .normal s10 4 :=
    runs_assign_iff.mpr ⟨i0 + 1, by simp [Expr.eval, BinOp.eval, s9, s8, hs7_high 71 (by decide),
      h71, show 1 < 2 ^ w by omega, show i0 + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hs10_eq (a : ℕ) (ha : a < st.regs 4) (hnf0 : ¬ Rcore.foot (coreHandle i0) (coreTok0 i0) a)
      (hneOld : a ≠ oldPtrs) : s10.mem a = st.mem a := by
    change Function.update s7.mem oldPtrs ret4 a = st.mem a
    rw [Function.update_of_ne hneOld, hs7_fr a (ha.trans_le hret4Lo), hresp4.2.2.2.1 a ha hnf0]
  have hs10_y4_foot (a : ℕ) (ha : Rcore.foot (coreHandle i0) y4 a) :
      (Rcore.foot (coreHandle i0) (coreTok0 i0) a ∨ (st.regs 4 ≤ a ∧ a < ret4)) ∧ a < ret4 ∧
        a ≠ oldPtrs := by
    rcases hresp4.2.2.2.2 a ha with h0 | ⟨hlo, hhi⟩
    · exact ⟨Or.inl h0, (hFoot0 a h0).trans_le hret4Lo,
        fun heq => hOldNotF0 0 (by omega) (by simpa [heq] using h0)⟩
    · exact ⟨Or.inr ⟨hlo, hhi⟩, hhi, by omega⟩
  have hlocY4_10 := hCoreLocal (coreHandle i0) (chainLevelOrdAbs chain i0) y4 s4.mem s10.mem
    (fun a ha => by
      obtain ⟨_, haLt, haNe⟩ := hs10_y4_foot a ha
      change s4.mem a = Function.update s7.mem oldPtrs ret4 a
      rw [Function.update_of_ne haNe, hs7_fr a haLt])
  -- Step 2: `collectLSFForestsLoop (op 2) 80` on `[i0 + 1, d)`
  have hs10_hz : ZeroFrom s10.mem hCopyEnd := fun a ha => by
    change Function.update s7.mem oldPtrs ret4 a = 0
    rw [Function.update_of_ne (by omega : a ≠ oldPtrs)]
    exact hz7 a ha
  have hs10_4 : s10.regs 4 = hCopyEnd := by simp [s10, s9]
  have hs10_cores : ∀ j, i0 + 1 ≤ j → j < CP.d →
      s10.mem (handleBase + j) = coreHandle j ∧
      s10.mem (branchBase + j) = chain.bran j ∧
      chain.bran j < CP.k ∧ coreHandle j < 2 ^ w ∧
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok0 j) s10.mem ∧
      SparseCoreOrdInput T CP.k (chain.lvlM j) chain.N₀ (chain.scState j) (chain.G j)
        (chain.levelOrd j) (chain.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → a < s10.regs 4) ∧
      (∀ r, i0 + 1 ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (levelMeta + CP.d + j)) ∧
      (handleBase + j < oldPtrs + (i0 + 1 - i0) ∨ oldPtrs + (CP.d - i0) ≤ handleBase + j) ∧
      (branchBase + j < oldPtrs + (i0 + 1 - i0) ∨ oldPtrs + (CP.d - i0) ≤ branchBase + j) ∧
      (levelMeta + CP.d + j < oldPtrs + (i0 + 1 - i0) ∨
        oldPtrs + (CP.d - i0) ≤ levelMeta + CP.d + j) ∧
      (∀ t, i0 + 1 - i0 ≤ t → t < CP.d - i0 →
        ¬ Rcore.foot (coreHandle j) (coreTok0 j) (oldPtrs + t)) ∧
      (DynGraphAt s10.mem (s10.mem (levelMeta + CP.d + j)) vCap eCap (chain.G j) ∧
        s10.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap ≤ s10.regs 4 ∧
        (∀ a, s10.mem (levelMeta + CP.d + j) ≤ a →
          a < s10.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap →
          (∀ r, i0 + 1 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
          (a < oldPtrs + (i0 + 1 - i0) ∨ oldPtrs + (CP.d - i0) ≤ a))) := by
    intro j hj1 hj2
    obtain ⟨hHj, hBj, hBrj, hChj, hRepj, hInj, hFootj, hNotj, hHOutj, hBOutj, hMOutj, hOldNotFj,
      hDGj, hDGEndj, hDGDisjj⟩ := hCores j (by omega) hj2
    have hlocJ := hCoreLocal (coreHandle j) (chainLevelOrdAbs chain j) (coreTok0 j) st.mem s10.mem
      (fun a ha => (hs10_eq a (hFootj a ha)
        (fun hf0 => hCoreDisj i0 j le_rfl hiLt (by omega) hj2 (by omega) a hf0 ha)
        (fun heq => hOldNotFj 0 (by omega) (by simpa [heq] using ha))).symm)
    have hGPtrEq : s10.mem (levelMeta + CP.d + j) = st.mem (levelMeta + CP.d + j) :=
      hs10_eq _ (by omega) (hNotj i0 le_rfl hiLt).2.2 (by rcases hMOutj with h | h <;> omega)
    refine ⟨(hs10_eq _ (by omega) (hNotj i0 le_rfl hiLt).1
        (by rcases hHOutj with h | h <;> omega)).trans hHj,
      (hs10_eq _ (by omega) (hNotj i0 le_rfl hiLt).2.1
        (by rcases hBOutj with h | h <;> omega)).trans hBj,
      hBrj, hChj, hlocJ.1 hRepj, hInj,
      fun a ha => (hFootj a ha).trans_le (by rw [hs10_4]; omega),
      fun r hr1 hr2 => hNotj r (by omega) hr2,
      by rcases hHOutj with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
      by rcases hBOutj with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
      by rcases hMOutj with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
      fun t ht1 ht2 => hOldNotFj t (by omega),
      ?_, by rw [hGPtrEq, hs10_4]; omega, ?_⟩
    · rw [hGPtrEq]
      exact dynGraphAt_of_agree hDGj (fun a ha1 ha2 => by
        obtain ⟨hNF, hOut⟩ := hDGDisjj a ha1 ha2
        exact hs10_eq a (by omega) (hNF i0 le_rfl hiLt) (by rcases hOut with h | h <;> omega))
    · rw [hGPtrEq]
      intro a ha1 ha2
      obtain ⟨hNF, hOut⟩ := hDGDisjj a ha1 ha2
      exact ⟨fun r hr1 hr2 => hNF r (by omega) hr2,
        by rcases hOut with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]⟩
  obtain ⟨s11, cLoop, tokLoop, rLoop, hs11_lo, hs11_hi, hz11, hTokLoop, _, hForests11, hs11_fr,
      hs11_regs, hcLoop⟩ :=
    collectLSFForestsLoopKFBL_runs (w := w) (L := L) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (first := i0 + 1) (baseIdx := i0) (dstReg := 80)
      (dstPtrs := oldPtrs) (handleBase := handleBase) (branchBase := branchBase)
      (levelMeta := levelMeta) (fmt := fmt) (P := P) (allocation := allocation)
      (p := p) (op := op) (ω := ω) (st := s10) chain coreHandle coreTok0 hCoreLocal (by decide)
      (by omega) (Nat.succ_le_of_lt hiLt) (by simp [s10])
      (by simp [s10, s9, s8, hs7_high 71 (by decide), h71])
      (by simp [s10, s9, s8, hs7_high 75 (by decide), h75])
      (by simp [s10, s9, s8, hs7_high 77 (by decide), h77])
      (by simp [s10, s9, s8, hs7_high 78 (by decide), h78])
      (by simp [s10, s9, s8, hs7_high 83 (by decide), h83])
      (by simp [s10, s9, s8, hs7_high 80 (by decide), h80])
      hkW hdW (by omega) (by rw [hs10_4]; omega) (by rw [hs10_4]; omega)
      (by rw [hs10_4]; omega) (by rw [hs10_4]; omega) (by rw [hs10_4]; omega)
      (by rw [hs10_4]; exact hs10_hz)
      (fun j hj1 hj2 => hFootAt j (by omega) hj2) hs10_cores
      (fun j₁ j₂ h1 h2 h3 h4 => hCoreDisj j₁ j₂ (by omega) h2 (by omega) h4)
  rw [hs10_4] at hs11_lo hs11_hi
  -- Step 3: `collectTermForestStmt 80`
  have hs11_eq_st (a : ℕ) (ha : a < st.regs 4)
      (hnf : ∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a)
      (hout : a < oldPtrs ∨ oldPtrs + (CP.d - i0) ≤ a) : s11.mem a = st.mem a := by
    have h1 := hs11_fr a (by rw [hs10_4]; omega) (fun r hr1 hr2 => hnf r (by omega) hr2)
      (by rcases hout with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
    exact h1.trans (hs10_eq a ha (hnf i0 le_rfl hiLt) (by rcases hout with h | h <;> omega))
  obtain ⟨hTHO, hTBO, hTLO, hTFO, hTLLt, hTFLt, hTNf, hTFDisj⟩ := hTermDisjCells
  obtain ⟨out, cTerm, rTerm, hcTerm, houtMem, houtRegs⟩ :=
    collectTermForestStmt_runs (w := w) (dstReg := 80) (dstPtrs := oldPtrs) (baseIdx := i0)
      (d := CP.d) (handleBase := handleBase) (branchBase := branchBase) (termHandle := termHandle)
      (lastBran := chain.lastBran) (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (p := p) (ω := ω) (st := s11)
      ((hs11_regs 80 (Or.inl (by decide))).trans (by simp [s10, s9, s8, hs7_high 80 (by decide), h80]))
      ((hs11_regs 71 (Or.inl (by decide))).trans (by simp [s10, s9, s8, hs7_high 71 (by decide), h71]))
      ((hs11_regs 75 (Or.inl (by decide))).trans (by simp [s10, s9, s8, hs7_high 75 (by decide), h75]))
      ((hs11_regs 77 (Or.inl (by decide))).trans (by simp [s10, s9, s8, hs7_high 77 (by decide), h77]))
      ((hs11_regs 78 (Or.inl (by decide))).trans (by simp [s10, s9, s8, hs7_high 78 (by decide), h78]))
      (by decide) (le_of_lt hiLt)
      ((hs11_eq_st _ (by omega) (fun r hr1 hr2 => (hTNf r hr1 hr2).1)
        (by rcases hTHO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermH)
      ((hs11_eq_st _ (by omega) (fun r hr1 hr2 => (hTNf r hr1 hr2).2.1)
        (by rcases hTBO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermB)
      ((hs11_eq_st _ hTLLt (fun r hr1 hr2 => (hTNf r hr1 hr2).2.2.1)
        (by rcases hTLO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermLsf)
      ((hs11_eq_st _ hTFLt (fun r hr1 hr2 => (hTNf r hr1 hr2).2.2.2)
        (by rcases hTFO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermFPtr)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hout4 : out.regs 4 = s11.regs 4 := houtRegs 4 (by decide) (by decide) (by decide)
  have hCopyLo : st.regs 4 ≤ s11.regs 4 := by omega
  have hCopyHi : s11.regs 4 ≤ st.regs 4 + 5 + dynGraphSize vcFi0 ecFi0 + 5 * (CP.d - (i0 + 1)) := by
    omega
  -- Where the new tokens of the cores `j > i0` lie
  have hLoopFoot (j : ℕ) (hj1 : i0 + 1 ≤ j) (hj2 : j < CP.d) (a : ℕ)
      (ha : Rcore.foot (coreHandle j) (tokLoop j) a) :
      ¬ Rcore.foot (coreHandle i0) y4 a ∧ forestSafe a ∧ a ≠ oldPtrs + (CP.d - i0) ∧
        a < s11.regs 4 := by
    obtain ⟨_, _, _, _, _, _, hFootj, _, _, _, _, hOldNotFj, _⟩ := hCores j (by omega) hj2
    rcases (hTokLoop j hj1 hj2).2 a ha with h0 | ⟨hlo, hhi⟩
    · refine ⟨fun hf => ?_, hSafeCore j (by omega) hj2 a h0,
        fun heq => hOldNotFj (CP.d - i0) (by omega) (heq ▸ h0), by have := hFootj a h0; omega⟩
      rcases (hs10_y4_foot a hf).1 with hi0 | ⟨hlo', _⟩
      · exact hCoreDisj i0 j le_rfl hiLt (by omega) hj2 (by omega) a hi0 h0
      · have := hFootj a h0; omega
    · rw [hs10_4] at hlo
      refine ⟨fun hf => ?_, hSafeAbove a (by omega), by omega, hhi⟩
      have := (hs10_y4_foot a hf).2.1; omega
  have hY4Pres : Rcore.rep (coreHandle i0) (chainLevelOrdAbs chain i0) y4 out.mem ∧
      Rcore.phi (coreHandle i0) y4 out.mem = Rcore.phi (coreHandle i0) y4 s4.mem := by
    have hloc := hCoreLocal (coreHandle i0) (chainLevelOrdAbs chain i0) y4 s10.mem out.mem
      (fun a ha => by
        obtain ⟨hIn, haLt, _⟩ := hs10_y4_foot a ha
        have hneTerm : a ≠ oldPtrs + (CP.d - i0) := by
          rcases hIn with h0 | ⟨hlo, _⟩
          · exact fun heq => hOldNotF0 (CP.d - i0) (by omega) (heq ▸ h0)
          · omega
        have hnfRest : ∀ r, i0 + 1 ≤ r → r < CP.d →
            ¬ Rcore.foot (coreHandle r) (coreTok0 r) a := fun r hr1 hr2 hf => by
          rcases hIn with h0 | ⟨hlo, _⟩
          · exact hCoreDisj i0 r le_rfl hiLt (by omega) hr2 (by omega) a h0 hf
          · have := (hCores r (by omega) hr2).2.2.2.2.2.2.1 a hf; omega
        have houtD : a < oldPtrs + (i0 + 1 - i0) ∨ oldPtrs + (CP.d - i0) ≤ a := by
          rcases hIn with h0 | ⟨hlo, _⟩
          · by_contra hcon; push Not at hcon
            have : a = oldPtrs + (a - oldPtrs) := by omega
            exact hOldNotF0 (a - oldPtrs) (by omega) (this ▸ h0)
          · exact Or.inr (by omega)
        rw [houtMem, Function.update_of_ne hneTerm,
          hs11_fr a (by rw [hs10_4]; omega) hnfRest houtD])
    exact ⟨hloc.1 (hlocY4_10.1 hrep4), hloc.2.symm.trans hlocY4_10.2.symm⟩
  -- The forest pointer list
  have hOldPtr0 : out.mem oldPtrs = ret4 := by
    rw [houtMem, Function.update_of_ne (by omega : oldPtrs ≠ oldPtrs + (CP.d - i0)),
      hs11_fr oldPtrs (by rw [hs10_4]; omega)
        (fun r hr1 hr2 => (hCores r (by omega) hr2).2.2.2.2.2.2.2.2.2.2.2.1 0 (by omega))
        (Or.inl (by omega))]
    simp [s10, s9, s8]
  have hCopyDGOut : DynGraphAt out.mem ret4 vcFi0 ecFi0 (T.lsfs (chain.scState i0) (chain.bran i0)).F.F :=
    dynGraphAt_of_agree hCopyDG (fun a ha1 ha2 => by
      rw [houtMem, Function.update_of_ne (by omega : a ≠ oldPtrs + (CP.d - i0)),
        hs11_fr a (by rw [hs10_4]; omega)
          (fun r hr1 hr2 hf => by have := (hCores r (by omega) hr2).2.2.2.2.2.2.1 a hf; omega)
          (Or.inr (by omega))]
      simp [s10, s9, s8, Function.update_of_ne (by omega : a ≠ oldPtrs)])
  clear hHOut0 hBOut0 hMOut0 hTHO hTBO hTLO hTFO
  have hForestListSafe :
      ∀ t (ht : t < (chainSuffixForests chain i0).length),
        ∃ vc ec,
          DynGraphAt out.mem (out.mem (oldPtrs + t)) vc ec (chainSuffixForests chain i0)[t] ∧
          out.mem (oldPtrs + t) + dynGraphSize vc ec ≤ out.regs 4 ∧
          (∀ e ∈ (chainSuffixForests chain i0)[t].E, e < intCap) ∧
          (∀ a, out.mem (oldPtrs + t) ≤ a → a < out.mem (oldPtrs + t) + dynGraphSize vc ec →
            ¬ Rcore.foot (coreHandle i0) y4 a ∧ forestSafe a) := by
    intro t ht
    rw [hout4]
    have ht' := ht
    rw [chainSuffixForests_length] at ht'
    by_cases ht0 : t = 0
    · subst ht0
      have h0Lt : 0 < CP.d - i0 := Nat.sub_pos_of_lt hiLt
      rw [chainSuffixForests_getElem_lt chain h0Lt, Nat.add_zero]
      refine ⟨vcFi0, ecFi0, ?_, ?_, hFi0Cap, fun a ha1 _ => ?_⟩
      · rw [hOldPtr0]; exact hCopyDGOut
      · rw [hOldPtr0]; omega
      · rw [hOldPtr0] at ha1
        exact ⟨fun hf => by have := (hs10_y4_foot a hf).2.1; omega,
          hSafeAbove a (hret4Lo.trans ha1)⟩
    · by_cases htLt : t < CP.d - i0
      · rw [chainSuffixForests_getElem_lt chain htLt]
        obtain ⟨vcT, ecT, hDGT, hEndT, hFootT⟩ := hForests11 (i0 + t) (by omega) (by omega)
        have hSub : i0 + t - i0 = t := by omega
        rw [hSub] at hDGT hEndT hFootT
        have hPtrT : out.mem (oldPtrs + t) = s11.mem (oldPtrs + t) := by
          rw [houtMem, Function.update_of_ne (by omega)]
        refine ⟨vcT, ecT, ?_, hPtrT.symm ▸ hEndT, hIntCap (i0 + t) (by omega) (by omega),
          fun a ha1 ha2 => ?_⟩
        · rw [hPtrT]
          exact dynGraphAt_of_agree hDGT (fun a ha1 ha2 => by
            rw [houtMem, Function.update_of_ne
              (hLoopFoot (i0 + t) (by omega) (by omega) a (hFootT a ha1 ha2)).2.2.1])
        · rw [hPtrT] at ha1 ha2
          obtain ⟨h1, h2, _⟩ := hLoopFoot (i0 + t) (by omega) (by omega) a (hFootT a ha1 ha2)
          exact ⟨h1, h2⟩
      · have htEq : t = CP.d - i0 := by omega
        subst htEq
        rw [chainSuffixForests_getElem_last]
        have hPtrL : out.mem (oldPtrs + (CP.d - i0)) = forestPtr := by
          rw [houtMem, Function.update_self]
        refine ⟨vcLast, ecLast, ?_, hPtrL.symm ▸ (hTermFEnd.trans hCopyLo), hTermFCap,
          fun a ha1 ha2 => ?_⟩
        · rw [hPtrL]
          exact dynGraphAt_of_agree hTermFDG (fun a ha1 ha2 => by
            obtain ⟨hNF, hOut, _⟩ := hTFDisj a ha1 ha2
            rw [houtMem, Function.update_of_ne (by rcases hOut with h | h <;> omega)]
            exact hs11_eq_st a (by omega) hNF
              (by rcases hOut with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
        · rw [hPtrL] at ha1 ha2
          obtain ⟨hNF, _, hSafeL⟩ := hTFDisj a ha1 ha2
          refine ⟨fun hf => ?_, hSafeL⟩
          rcases (hs10_y4_foot a hf).1 with h0 | ⟨hlo, _⟩
          · exact hNF i0 le_rfl hiLt h0
          · omega
  have hForestList :
      ForestPtrListAt out.mem oldPtrs (chainSuffixForests chain i0) intCap (out.regs 4) :=
    ⟨by rw [chainSuffixForests_length]; omega, fun t ht => by
      obtain ⟨vc, ec, hG, hE, hC, _⟩ := hForestListSafe t ht
      exact ⟨vc, ec, hG, hE, hC⟩⟩
  -- Compose runs and cost
  have rAll : Runs w p ω (shiftDeepCollectOldKFBL (op 2)) st .normal out
      (5 + (5 + (7 + (c4 + (5 + (2 + (cCopy + (3 + (2 + (4 + (cLoop + cTerm + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, cCopy, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 3, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 4, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, cLoop, cTerm, rLoop, rTerm, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨out, _, vcFi0, ecFi0, y4, rAll, hout4.symm ▸ hCopyLo, hout4.symm ▸ hCopyHi, hFcap4,
    fun a ha => by
      rw [hout4] at ha; rw [houtMem, Function.update_of_ne (by omega : a ≠ oldPtrs + (CP.d - i0))]
      exact hz11 a ha,
    hOldPtr0.symm ▸ hCopyDGOut, hOldPtr0.symm ▸ hret4Lo,
    fun a ha1 _ hf => by
      rw [hOldPtr0] at ha1
      have := (hs10_y4_foot a hf).2.1; omega,
    hForestList, hForestListSafe,
    hY4Pres.1, fun a ha => by
      rw [hout4]
      rcases (hs10_y4_foot a ha).1 with h0 | ⟨hlo, hhi⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hlo, by omega⟩,
    fun a ha hnf hout => by
      rw [houtMem, Function.update_of_ne (by rcases hout with h | h <;> omega)]
      exact hs11_eq_st a ha hnf (by rcases hout with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]),
    fun r hr => (houtRegs r (by omega) (by omega) (by omega)).trans
      ((hs11_regs r (Or.inl hr)).trans (by simp [s10, s9, s8, Function.update_of_ne (by omega : r ≠ 20),
        Function.update_of_ne (by omega : r ≠ 4), hs7_high r hr])),
    ?_⟩
  -- Cost telescopes `Rcore.phi` on `i0` and spends old `Rcore.phi` on `[i0 + 1, d)`
  have hPhiRest :
      (Finset.Ico (i0 + 1) CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) s10.mem) =
      (Finset.Ico (i0 + 1) CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) :=
    Finset.sum_congr rfl (fun j hj => by
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      obtain ⟨_, _, _, _, _, _, hFootj, _, _, _, _, hOldNotFj, _⟩ := hCores j (by omega) hj2
      have hlocJ := hCoreLocal (coreHandle j) (chainLevelOrdAbs chain j) (coreTok0 j) st.mem s10.mem
        (fun a ha => (hs10_eq a (hFootj a ha)
          (fun hf0 => hCoreDisj i0 j le_rfl hiLt (by omega) hj2 (by omega) a hf0 ha)
          (fun heq => hOldNotFj 0 (by omega) (by simpa [heq] using ha))).symm)
      exact hlocJ.2.symm)
  have hIcoSplit :
      (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) =
      Rcore.phi (coreHandle i0) (coreTok0 i0) st.mem +
      (Finset.Ico (i0 + 1) CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) := by
    have hEq : Finset.Ico i0 CP.d = insert i0 (Finset.Ico (i0 + 1) CP.d) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hEq, Finset.sum_insert (by simp)]
  have hMulSplit : (CP.d - i0) * (P.readout + 48) =
      (CP.d - (i0 + 1)) * (P.readout + 48) + (P.readout + 48) := by
    have : CP.d - i0 = (CP.d - (i0 + 1)) + 1 := by omega
    rw [this]; ring
  rw [hY4Pres.2, hIcoSplit, hMulSplit]
  rw [hPhiRest] at hcLoop
  change c4 + Rcore.phi (coreHandle i0) y4 s4.mem ≤
    P.readout + 5 + Rcore.phi (coreHandle i0) (coreTok0 i0) st.mem at hc4
  dsimp only [chainLevelOrdAbs] at hcCopy
  omega

end MinCostFlow.MinRatio
