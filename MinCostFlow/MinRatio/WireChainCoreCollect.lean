module

public import MinCostFlow.MinRatio.WireChainCoreOps
import WordRAM.Tactic

/-!
# Copying active LSF forests across levels `0 .. d - 1` (`WireChainCoreCollect`)

Provides `collectCopyLSFForestsLoop` and `collectCopyLSFForestsLoop_runs`, which read and copy
every level `0 .. d - 1`'s active LSF forest via `copyGraphFromHeader` into caller-owned memory
so subsequent in-place op-`0` updates on levels `0 .. d - 1` cannot overwrite the old-forest
snapshots used for tree-edit diffing.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Collect and copy every level `0 .. d - 1`'s active LSF forest via `copyGraphFromHeader` into
caller-owned memory, storing pointers in `mem[reg dstReg + j]`. Safe across subsequent in-place
op-`0` updates on every level `0 .. d - 1`. -/
@[expose] def collectCopyLSFForestsLoop (readLSF dstReg : ℕ) : Stmt :=
  forRange 19 (.const 0) (.reg 75)
    (.assign 3 (.load (.bin .add (.reg 77) (.reg 19))) ;;
     .assign 2 (.load (.bin .add (.reg 78) (.reg 19))) ;;
     .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 19))) ;;
     ordCoreReadLSFStmt readLSF ;;
     .assign 6 (.load (.bin .add (.reg 4) (.const 1))) ;;
     .assign 4 (.reg 5) ;;
     copyGraphFromHeader ;;
     .store (.bin .add (.reg dstReg) (.reg 19)) (.reg 6) ;;
     .assign 4 (.reg 5))

theorem collectCopyLSFForestsLoop_noRand (readLSF dstReg : ℕ) :
    (collectCopyLSFForestsLoop readLSF dstReg).NoRand := by
  simp [collectCopyLSFForestsLoop, forRange, forUp, ordCoreReadLSFStmt_noRand, copyGraphFromHeader,
    readGraphCopySize, copyReadoutGraphAtHeap, copyReadoutGraph, copyWordsStmt, Stmt.NoRand]

/-- Loop invariant for `collectCopyLSFForestsLoop_runs`. -/
private structure CollectCopyLSFInv {w L dstReg dstPtrs handleBase branchBase levelMeta dgCap : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (chain : ChainState T CP)
    (coreHandle : ℕ → ℕ) (tok0 : ℕ → Rcore.τ) (st0 : State)
    (cur : ℕ) (s : State) (pot : ℕ) : Prop where
  r19 : s.regs 19 = cur
  r75 : s.regs 75 = CP.d
  r77 : s.regs 77 = handleBase
  r78 : s.regs 78 = branchBase
  r83 : s.regs 83 = levelMeta
  rDst : s.regs dstReg = dstPtrs
  rKeep : ∀ r, 70 ≤ r → s.regs r = st0.regs r
  hLo : st0.regs 4 ≤ s.regs 4
  hHi : s.regs 4 ≤ st0.regs 4 + cur * (5 + dgCap)
  hz : ZeroFrom s.mem (s.regs 4)
  toks : ∃ tok : ℕ → Rcore.τ,
    (∀ j < CP.d,
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (tok j) s.mem ∧
      (j < cur → ∀ a, Rcore.foot (coreHandle j) (tok j) a →
        Rcore.foot (coreHandle j) (tok0 j) a ∨ (st0.regs 4 ≤ a ∧ a < s.regs 4)) ∧
      (cur ≤ j → tok j = tok0 j)) ∧
    (∀ j₁ < CP.d, ∀ j₂ < CP.d, j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (tok j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (tok j₂) a) ∧
    (∀ t < cur, ∃ vc ec,
      DynGraphAt s.mem (s.mem (dstPtrs + t)) vc ec (T.lsfs (chain.scState t) (chain.bran t)).F.F ∧
      st0.regs 4 ≤ s.mem (dstPtrs + t) ∧
      s.mem (dstPtrs + t) + dynGraphSize vc ec ≤ s.regs 4 ∧
      ∀ r < CP.d, ∀ a, s.mem (dstPtrs + t) ≤ a → a < s.mem (dstPtrs + t) + dynGraphSize vc ec →
        ¬ Rcore.foot (coreHandle r) (tok r) a) ∧
    pot = (Finset.range CP.d).sum (fun j => Rcore.phi (coreHandle j) (tok j) s.mem)
  frame : ∀ a < st0.regs 4,
    (∀ j < cur, ¬ Rcore.foot (coreHandle j) (tok0 j) a) →
    (a < dstPtrs ∨ dstPtrs + cur ≤ a) → s.mem a = st0.mem a

/-- Execute `collectCopyLSFForestsLoop` over all levels `0 .. d - 1`. Every copied forest lies inside
`[st.regs 4, out.regs 4)` and is disjoint from all core footprints and all addresses `< st.regs 4`. -/
theorem collectCopyLSFForestsLoop_runs
    {w L capExp init dstReg dstPtrs handleBase branchBase levelMeta dgCap : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (chain : ChainState T CP) (coreHandle : ℕ → ℕ) (coreTok0 : ℕ → Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hDstReg : 70 ≤ dstReg) (hDst : st.regs dstReg = dstPtrs)
    (h75 : st.regs 75 = CP.d) (h77 : st.regs 77 = handleBase)
    (h78 : st.regs 78 = branchBase) (h83 : st.regs 83 = levelMeta)
    (hkW : CP.k < 2 ^ w) (hdW : CP.d < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hMetaEnd : levelMeta + 2 * CP.d ≤ st.regs 4)
    (hHEnd : handleBase + CP.d ≤ st.regs 4) (hBEnd : branchBase + CP.d ≤ st.regs 4)
    (hDstEnd : dstPtrs + CP.d ≤ st.regs 4)
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hRoom : st.regs 4 + CP.d * (5 + dgCap) < 2 ^ w)
    (hCoreImpl : ∀ j < CP.d, ∀ vc ec,
      Rcore.Implements w p init op
        (sparseCoreOrdMachineContractK fmt L T (chain.G j) CP.k (chain.lvlM j) chain.N₀
          vc ec capExp P (allocation j)))
    (hCores : ∀ j < CP.d,
      st.mem (handleBase + j) = coreHandle j ∧
      st.mem (branchBase + j) = chain.bran j ∧
      chain.bran j < CP.k ∧ coreHandle j < 2 ^ w ∧
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok0 j) st.mem ∧
      SparseCoreOrdInput T CP.k (chain.lvlM j) chain.N₀ (chain.scState j) (chain.G j)
        (chain.levelOrd j) (chain.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → a < st.regs 4) ∧
      (∀ r < CP.d,
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (levelMeta + CP.d + j)) ∧
      (handleBase + j < dstPtrs ∨ dstPtrs + CP.d ≤ handleBase + j) ∧
      (branchBase + j < dstPtrs ∨ dstPtrs + CP.d ≤ branchBase + j) ∧
      (levelMeta + CP.d + j < dstPtrs ∨ dstPtrs + CP.d ≤ levelMeta + CP.d + j) ∧
      (∀ t < CP.d, ¬ Rcore.foot (coreHandle j) (coreTok0 j) (dstPtrs + t)) ∧
      (∃ vc ec,
        DynGraphAt st.mem (st.mem (levelMeta + CP.d + j)) vc ec (chain.G j) ∧
        st.mem (levelMeta + CP.d + j) + dynGraphSize vc ec ≤ st.regs 4 ∧
        (∀ a, st.mem (levelMeta + CP.d + j) ≤ a →
          a < st.mem (levelMeta + CP.d + j) + dynGraphSize vc ec →
          (∀ r < CP.d, ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
          (a < dstPtrs ∨ dstPtrs + CP.d ≤ a))))
    (hCoreDisj : ∀ j₁ < CP.d, ∀ j₂ < CP.d, j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (coreTok0 j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (coreTok0 j₂) a)
    (hOp2 : ∀ j < CP.d, ∀ m h ret vcF ecF Lw,
      LSFAt m h vcF ecF fmt.limbBits Lw fmt.precision (chain.G j).E
        (T.lsfs (chain.scState j) (chain.bran j)) →
      h ≤ ret → ret ≤ h + 5 →
      m (h + 1) + dynGraphSize vcF ecF ≤ ret ∧ dynGraphSize vcF ecF ≤ dgCap) :
    ∃ (out : State) (cost : ℕ) (coreTok' : ℕ → Rcore.τ),
      Runs w p ω (collectCopyLSFForestsLoop (op 2) dstReg) st .normal out cost ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + CP.d * (5 + dgCap) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ j < CP.d, ∃ vc ec,
        DynGraphAt out.mem (out.mem (dstPtrs + j)) vc ec (T.lsfs (chain.scState j) (chain.bran j)).F.F ∧
        st.regs 4 ≤ out.mem (dstPtrs + j) ∧
        out.mem (dstPtrs + j) + dynGraphSize vc ec ≤ out.regs 4 ∧
        ∀ r < CP.d, ∀ a, out.mem (dstPtrs + j) ≤ a → a < out.mem (dstPtrs + j) + dynGraphSize vc ec →
          ¬ Rcore.foot (coreHandle r) (coreTok' r) a) ∧
      (∀ j < CP.d,
        Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok' j) out.mem ∧
        (∀ a, Rcore.foot (coreHandle j) (coreTok' j) a →
          Rcore.foot (coreHandle j) (coreTok0 j) a ∨ (st.regs 4 ≤ a ∧ a < out.regs 4))) ∧
      (∀ j₁ < CP.d, ∀ j₂ < CP.d, j₁ ≠ j₂ →
        ∀ a, Rcore.foot (coreHandle j₁) (coreTok' j₁) a →
          ¬ Rcore.foot (coreHandle j₂) (coreTok' j₂) a) ∧
      (∀ a < st.regs 4, (∀ j < CP.d, ¬ Rcore.foot (coreHandle j) (coreTok0 j) a) →
        (a < dstPtrs ∨ dstPtrs + CP.d ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      cost + (Finset.range CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) out.mem) ≤
        CP.d * (P.readout + 17 * dgCap + 100) + 15 +
          (Finset.range CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) := by
  have hw1 : 1 < 2 ^ w := by omega
  let Inv := CollectCopyLSFInv (w := w) (L := L) (dstReg := dstReg) (dstPtrs := dstPtrs)
    (handleBase := handleBase) (branchBase := branchBase) (levelMeta := levelMeta) (dgCap := dgCap)
    (fmt := fmt) Rcore chain coreHandle coreTok0 st
  let pot0 := (Finset.range CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem)
  let sInit := { st with regs := Function.update st.regs 19 0 }
  have rInit : Runs w p ω (.assign 19 (.const 0)) st .normal sInit 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hInv0 : Inv 0 sInit pot0 :=
    { r19 := by simp [sInit], r75 := by simp [sInit, h75], r77 := by simp [sInit, h77],
      r78 := by simp [sInit, h78], r83 := by simp [sInit, h83],
      rDst := by simp [sInit, Function.update_of_ne (by omega : dstReg ≠ 19), hDst],
      rKeep := fun r hr => Function.update_of_ne (by omega) _ _,
      hLo := le_rfl, hHi := by simp [sInit], hz := hz0,
      toks := ⟨coreTok0, fun j hj => ⟨(hCores j hj).2.2.2.2.1, fun h => by omega, fun _ => rfl⟩,
        hCoreDisj, fun _ h => by omega, rfl⟩,
      frame := fun _ _ _ _ => rfl }
  let body : Stmt :=
    .assign 3 (.load (.bin .add (.reg 77) (.reg 19))) ;;
    .assign 2 (.load (.bin .add (.reg 78) (.reg 19))) ;;
    .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 19))) ;;
    ordCoreReadLSFStmt (op 2) ;;
    .assign 6 (.load (.bin .add (.reg 4) (.const 1))) ;;
    .assign 4 (.reg 5) ;;
    copyGraphFromHeader ;;
    .store (.bin .add (.reg dstReg) (.reg 19)) (.reg 6) ;;
    .assign 4 (.reg 5)
  suffices hUp : ∀ (rem cur : ℕ) (s : State) (pot : ℕ),
      cur + rem = CP.d → Inv cur s pot →
      ∃ out c potEnd,
        Runs w p ω (forUp 19 (.reg 75) body) s .normal out c ∧
        Inv CP.d out potEnd ∧
        c + potEnd ≤ rem * (P.readout + 17 * dgCap + 100) + pot + 4 by
    obtain ⟨out, c, potEnd, rLoop, hEnd, hc⟩ := hUp CP.d 0 sInit pot0 (by omega) hInv0
    obtain ⟨tokEnd, hTokRep, hTokDisj, hForests, hPotEq⟩ := hEnd.toks
    refine ⟨out, 2 + c + 1, tokEnd, runs_seq_iff.mpr (Or.inr ⟨sInit, 2, c, rInit, rLoop, rfl⟩),
      hEnd.hLo, hEnd.hHi, hEnd.hz, hForests,
      fun j hj => ⟨(hTokRep j hj).1, (hTokRep j hj).2.1 hj⟩,
      hTokDisj, hEnd.frame, hEnd.rKeep, by rw [← hPotEq]; omega⟩
  intro rem
  induction rem with
  | zero =>
    intro cur s pot hsum hInv
    have hcur : cur = CP.d := by omega
    subst hcur
    refine ⟨s, 4, pot, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hInv.r19, hInv.r75],
      rfl, rfl, by simp [Expr.size]⟩), hInv, by simp; omega⟩
  | succ rem ih =>
    intro cur s pot hsum hInv
    have hlt : cur < CP.d := by omega
    obtain ⟨tok, hTokRep, hTokDisj, hForests, hPotEq⟩ := hInv.toks
    obtain ⟨hHCell, hBCell, hBrLt, hChW, _, hInCur, hFoot0Cur, hNotCell, hHOutD, hBOutD,
      hMOutD, hDstNotF, ⟨vcG, ecG, hDG0, hDGEnd0, hDGDisj0⟩⟩ := hCores cur hlt
    have hTokCurEq : tok cur = coreTok0 cur := (hTokRep cur hlt).2.2 le_rfl
    have hHCellS : s.mem (handleBase + cur) = coreHandle cur :=
      (hInv.frame _ (by omega) (fun r hr => (hNotCell r (by omega)).1)
        (by rcases hHOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hHCell
    have hBCellS : s.mem (branchBase + cur) = chain.bran cur :=
      (hInv.frame _ (by omega) (fun r hr => (hNotCell r (by omega)).2.1)
        (by rcases hBOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hBCell
    have hGPtrS : s.mem (levelMeta + CP.d + cur) = st.mem (levelMeta + CP.d + cur) :=
      hInv.frame _ (by omega) (fun r hr => (hNotCell r (by omega)).2.2)
        (by rcases hMOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
    have hDGS : DynGraphAt s.mem (st.mem (levelMeta + CP.d + cur)) vcG ecG (chain.G cur) :=
      dynGraphAt_of_agree hDG0 (fun a ha1 ha2 => by
        obtain ⟨hNF, hOutD⟩ := hDGDisj0 a ha1 ha2
        exact hInv.frame a (by omega) (fun r hr => hNF r (by omega))
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
      runs_assign_iff.mpr ⟨st.mem (levelMeta + CP.d + cur), by
        simp [Expr.eval, BinOp.eval, s2, s1, hInv.r83, hInv.r75, hInv.r19,
          show levelMeta + CP.d < 2 ^ w by omega, show levelMeta + CP.d + cur < 2 ^ w by omega,
          hGPtrS], rfl, rfl, rfl⟩
    have hCurMul : (cur + 1) * (5 + dgCap) ≤ CP.d * (5 + dgCap) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
    have hCurRoom : s.regs 4 + 5 + dgCap < 2 ^ w := by
      have hhi := hInv.hHi; rw [Nat.succ_mul] at hCurMul; omega
    have hLo0 := hInv.hLo
    obtain ⟨s4, ret4, cOp2, yCur, r4, h4_5, hRep4, _, ⟨vcF, ecF, hLSF4⟩, hResp4, hcOp2, h4Regs⟩ :=
      ordCoreReadLSFK_runs (st := s3) (ω := ω) (hCoreImpl cur hlt vcG ecG)
        (by simp [s3, s2]) (by simp [s3, s2, s1]) (by simp [s3]) (by simp [s3, s2, s1])
        hBrLt hkW hChW hDGS (by omega) (hTokCurEq ▸ (hTokRep cur hlt).1) hInCur
        (fun a ha => (hFoot0Cur a ha).trans_le hInv.hLo) hInv.hz (by omega)
    obtain ⟨hRetLo, hRetHi, hz4, hFr4, hFoot4⟩ := hResp4
    obtain ⟨hFEnd4, hFDg4⟩ := hOp2 cur hlt s4.mem (s.regs 4) ret4 vcF ecF _ hLSF4 hRetLo hRetHi
    let fPtr := s4.mem (s.regs 4 + 1)
    let s5 := { s4 with regs := Function.update s4.regs 6 fPtr }
    let s6 := { s5 with regs := Function.update s5.regs 4 ret4 }
    have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 4) (.const 1)))) s4 .normal s5 5 :=
      runs_assign_iff.mpr ⟨fPtr, by simp [Expr.eval, BinOp.eval, h4Regs 4 (by decide), s3, s2, s1,
        hw1, show s.regs 4 + 1 < 2 ^ w by omega, fPtr], rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 4 (.reg 5)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨ret4, by simp [Expr.eval, s5, h4_5], rfl, rfl, rfl⟩
    obtain ⟨s7, cCopy, r7, hCopyDG7, h7_6, h7_5, hz7, hFr7, _, hcCopy, h7Regs⟩ :=
      copyGraphFromHeader_runs (p := p) (st := s6) (ω := ω) (by simp [s6, s5, fPtr])
        (by simp [s6, s5, h4_5]) hLSF4.2.1 hFEnd4 (by omega) hw9 hz4
    let newHeap := ret4 + dynGraphSize vcF ecF
    let s8 := { s7 with mem := Function.update s7.mem (dstPtrs + cur) ret4 }
    let s9 := { s8 with regs := Function.update s8.regs 4 newHeap }
    have h7Keep (r : ℕ) (hr : 70 ≤ r) : s7.regs r = st.regs r := by
      rw [h7Regs r (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp only [s6, s5, Function.update_of_ne (by omega : r ≠ 4), Function.update_of_ne (by omega : r ≠ 6)]
      rw [h4Regs r (by omega)]
      simp only [s3, s2, s1, Function.update_of_ne (by omega : r ≠ 6),
        Function.update_of_ne (by omega : r ≠ 2), Function.update_of_ne (by omega : r ≠ 3)]
      exact hInv.rKeep r hr
    have h7_19 : s7.regs 19 = cur := by
      rw [h7Regs 19 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp only [s6, s5, Function.update_of_ne (by decide : (19 : ℕ) ≠ 4),
        Function.update_of_ne (by decide : (19 : ℕ) ≠ 6)]
      rw [h4Regs 19 (by decide)]; simp [s3, s2, s1, hInv.r19]
    have r8 : Runs w p ω (.store (.bin .add (.reg dstReg) (.reg 19)) (.reg 6)) s7 .normal s8 5 :=
      runs_store_iff.mpr ⟨dstPtrs + cur, ret4,
        by simp [Expr.eval, BinOp.eval, h7Keep dstReg hDstReg, hDst, h7_19,
          show dstPtrs + cur < 2 ^ w by omega],
        by simp [Expr.eval, h7_6], rfl, rfl, rfl⟩
    have r9 : Runs w p ω (.assign 4 (.reg 5)) s8 .normal s9 2 :=
      runs_assign_iff.mpr ⟨newHeap, by simp [Expr.eval, s8, h7_5, newHeap], rfl, rfl, rfl⟩
    have h9Eq4 (a : ℕ) (ha : a < ret4) (hne : a ≠ dstPtrs + cur) : s9.mem a = s4.mem a :=
      (Function.update_of_ne hne _ _).trans (hFr7 a ha)
    let tok' : ℕ → Rcore.τ := Function.update tok cur yCur
    have hCurNotDst : ¬ Rcore.foot (coreHandle cur) yCur (dstPtrs + cur) := fun hf => by
      rcases hFoot4 _ hf with h0 | ⟨hlo, _⟩
      · exact hDstNotF cur hlt h0
      · have := hInv.hLo; omega
    have hCurLoc := hCoreLocal (coreHandle cur) (chainLevelOrdAbs chain cur) yCur s4.mem s9.mem
      (fun a ha => by
        have hltRet : a < ret4 := by
          rcases hFoot4 a ha with h0 | ⟨_, hhi⟩
          · exact (hFoot0Cur a h0).trans_le (hInv.hLo.trans hRetLo)
          · exact hhi
        exact (h9Eq4 a hltRet (fun h => hCurNotDst (h ▸ ha))).symm)
    have hOtherLoc (r : ℕ) (hr : r < CP.d) (hne : r ≠ cur) :
        (Rcore.rep (coreHandle r) (chainLevelOrdAbs chain r) (tok r) s.mem →
         Rcore.rep (coreHandle r) (chainLevelOrdAbs chain r) (tok r) s9.mem) ∧
        Rcore.phi (coreHandle r) (tok r) s.mem = Rcore.phi (coreHandle r) (tok r) s9.mem :=
      hCoreLocal (coreHandle r) (chainLevelOrdAbs chain r) (tok r) s.mem s9.mem (fun a ha => by
        have haLtS : a < s.regs 4 := by
          by_cases hrc : r < cur
          · rcases (hTokRep r hr).2.1 hrc a ha with h0 | ⟨_, hhi⟩
            · exact ((hCores r hr).2.2.2.2.2.2.1 a h0).trans_le hInv.hLo
            · exact hhi
          · rw [(hTokRep r hr).2.2 (by omega)] at ha
            exact ((hCores r hr).2.2.2.2.2.2.1 a ha).trans_le hInv.hLo
        have hneDst : a ≠ dstPtrs + cur := by
          intro hEq; subst hEq
          by_cases hrc : r < cur
          · rcases (hTokRep r hr).2.1 hrc _ ha with h0 | ⟨hlo, _⟩
            · exact (hCores r hr).2.2.2.2.2.2.2.2.2.2.2.1 cur hlt h0
            · omega
          · rw [(hTokRep r hr).2.2 (by omega)] at ha
            exact (hCores r hr).2.2.2.2.2.2.2.2.2.2.2.1 cur hlt ha
        have hNotCur : ¬ Rcore.foot (coreHandle cur) (coreTok0 cur) a :=
          fun hf => hTokDisj r hr cur hlt hne a ha (hTokCurEq.symm ▸ hf)
        exact ((h9Eq4 a (haLtS.trans_le hRetLo) hneDst).trans (hFr4 a haLtS hNotCur)).symm)
    let potNext := (Finset.range CP.d).sum (fun j => Rcore.phi (coreHandle j) (tok' j) s9.mem)
    have hPotStep : cOp2 + potNext ≤ P.readout + 5 + pot := by
      have hSplit (f : ℕ → ℕ) : (Finset.range CP.d).sum f =
          f cur + ((Finset.range CP.d).erase cur).sum f :=
        (Finset.add_sum_erase _ _ (Finset.mem_range.mpr hlt)).symm
      have hEraseEq :
          ((Finset.range CP.d).erase cur).sum (fun j => Rcore.phi (coreHandle j) (tok' j) s9.mem) =
          ((Finset.range CP.d).erase cur).sum (fun j => Rcore.phi (coreHandle j) (tok j) s.mem) :=
        Finset.sum_congr rfl (fun j hj => by
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hj
          simp only [tok', Function.update_of_ne hne]
          exact (hOtherLoc j (Finset.mem_range.mp hmem) hne).2.symm)
      dsimp only [potNext]
      rw [hSplit, hEraseEq, hPotEq, hSplit]
      simp only [tok', Function.update_self]
      rw [← hCurLoc.2]
      have hcurPhi : cOp2 + Rcore.phi (coreHandle cur) yCur s4.mem ≤
          P.readout + 5 + Rcore.phi (coreHandle cur) (coreTok0 cur) s.mem := hcOp2
      rw [hTokCurEq]
      omega
    let sNext := { s9 with regs := Function.update s9.regs 19 (cur + 1) }
    have rBody : Runs w p ω body s .normal s9
        (5 + (5 + (7 + (cOp2 + (5 + (2 + (cCopy + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, cOp2, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, cCopy, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, 5, 2, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have rInc : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.const 1))) s9 .normal sNext 4 :=
      runs_assign_iff.mpr ⟨cur + 1, by
        simp [Expr.eval, BinOp.eval, s9, s8, h7_19, hw1, show cur + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hInvNext : Inv (cur + 1) sNext potNext := by
      refine
        { r19 := by simp [sNext], r75 := by simp [sNext, s9, s8, h7Keep 75 (by decide), h75],
          r77 := by simp [sNext, s9, s8, h7Keep 77 (by decide), h77],
          r78 := by simp [sNext, s9, s8, h7Keep 78 (by decide), h78],
          r83 := by simp [sNext, s9, s8, h7Keep 83 (by decide), h83],
          rDst := by simp [sNext, s9, s8, Function.update_of_ne (by omega : dstReg ≠ 19),
            Function.update_of_ne (by omega : dstReg ≠ 4), h7Keep dstReg hDstReg, hDst],
          rKeep := fun r hr => by
            simp only [sNext, s9, s8, Function.update_of_ne (by omega : r ≠ 19),
              Function.update_of_ne (by omega : r ≠ 4)]
            exact h7Keep r hr,
          hLo := by simp only [sNext, s9, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19),
            Function.update_self]; have := hInv.hLo; dsimp [newHeap]; omega,
          hHi := by simp only [sNext, s9, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19),
            Function.update_self]; have hhi := hInv.hHi; dsimp [newHeap]; rw [Nat.succ_mul]; omega,
          hz := fun a ha => by
            simp only [sNext, s9, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19),
              Function.update_self] at ha
            exact (Function.update_of_ne (by dsimp [newHeap] at ha; have := hInv.hLo; omega : a ≠ dstPtrs + cur) _ _).trans
              (hz7 a (by dsimp [newHeap] at ha; exact ha)),
          toks := ⟨tok', ?_, ?_, ?_, rfl⟩,
          frame := fun a ha hNotF hOutD => by
            have hneCur : a ≠ dstPtrs + cur := by rcases hOutD with h | h <;> omega
            exact (h9Eq4 a (ha.trans_le (hInv.hLo.trans hRetLo)) hneCur).trans
              ((hFr4 a (ha.trans_le hInv.hLo) (hNotF cur (Nat.lt_succ_self cur))).trans
                (hInv.frame a ha (fun j hj => hNotF j (Nat.lt_succ_of_lt hj))
                  (by rcases hOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))) }
      · intro j hj
        by_cases hjc : j = cur
        · subst hjc
          simp only [tok', Function.update_self]
          refine ⟨hCurLoc.1 hRep4, fun _ a ha => ?_, fun h => by omega⟩
          rcases hFoot4 a ha with h0 | ⟨hlo, hhi⟩
          · exact Or.inl h0
          · exact Or.inr ⟨hInv.hLo.trans hlo, by
              simp only [sNext, s9, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]
              dsimp [newHeap]; omega⟩
        · simp only [tok', Function.update_of_ne hjc]
          refine ⟨(hOtherLoc j hj hjc).1 (hTokRep j hj).1, fun hlt' a ha => ?_,
            fun hge => (hTokRep j hj).2.2 (by omega)⟩
          rcases (hTokRep j hj).2.1 (by omega) a ha with h0 | ⟨hlo, hhi⟩
          · exact Or.inl h0
          · exact Or.inr ⟨hlo, by
              simp only [sNext, s9, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]
              dsimp [newHeap]; omega⟩
      · intro j₁ hj₁ j₂ hj₂ hne a ha1 ha2
        by_cases h1 : j₁ = cur
        · subst h1; simp only [tok', Function.update_self] at ha1
          simp only [tok', Function.update_of_ne (Ne.symm hne)] at ha2
          have ha2Lt : a < s.regs 4 := by
            by_cases h2c : j₂ < j₁
            · rcases (hTokRep j₂ hj₂).2.1 h2c a ha2 with h0 | ⟨_, hhi⟩
              · exact ((hCores j₂ hj₂).2.2.2.2.2.2.1 a h0).trans_le hInv.hLo
              · exact hhi
            · rw [(hTokRep j₂ hj₂).2.2 (by omega)] at ha2
              exact ((hCores j₂ hj₂).2.2.2.2.2.2.1 a ha2).trans_le hInv.hLo
          rcases hFoot4 a ha1 with h0 | ⟨hlo, _⟩
          · exact hTokDisj j₁ hj₁ j₂ hj₂ hne a (hTokCurEq.symm ▸ h0) ha2
          · omega
        · by_cases h2 : j₂ = cur
          · subst h2; simp only [tok', Function.update_self] at ha2
            simp only [tok', Function.update_of_ne hne] at ha1
            have ha1Lt : a < s.regs 4 := by
              by_cases h1c : j₁ < j₂
              · rcases (hTokRep j₁ hj₁).2.1 h1c a ha1 with h0 | ⟨_, hhi⟩
                · exact ((hCores j₁ hj₁).2.2.2.2.2.2.1 a h0).trans_le hInv.hLo
                · exact hhi
              · rw [(hTokRep j₁ hj₁).2.2 (by omega)] at ha1
                exact ((hCores j₁ hj₁).2.2.2.2.2.2.1 a ha1).trans_le hInv.hLo
            rcases hFoot4 a ha2 with h0 | ⟨hlo, _⟩
            · exact hTokDisj j₁ hj₁ j₂ hj₂ hne a ha1 (hTokCurEq.symm ▸ h0)
            · omega
          · simp only [tok', Function.update_of_ne h1, Function.update_of_ne h2] at ha1 ha2
            exact hTokDisj j₁ hj₁ j₂ hj₂ hne a ha1 ha2
      · intro t ht
        by_cases htc : t = cur
        · subst htc
          refine ⟨vcF, ecF, ?_, ?_, ?_, ?_⟩
          · have hEq : sNext.mem (dstPtrs + t) = ret4 := by simp [sNext, s9, s8]
            rw [hEq]
            exact dynGraphAt_of_agree hCopyDG7 (fun a ha1 _ =>
              Function.update_of_ne (by have := hInv.hLo; omega : a ≠ dstPtrs + t) _ _)
          · simp [sNext, s9, s8]; have := hInv.hLo; omega
          · simp only [sNext, s9, s8, Function.update_self, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19)]
            dsimp [newHeap]; omega
          · intro r hr a ha1 ha2
            simp only [sNext, s9, s8, Function.update_self] at ha1 ha2
            by_cases hrc : r = t
            · subst hrc; simp only [tok', Function.update_self]; intro hf
              rcases hFoot4 a hf with h0 | ⟨_, hhi⟩
              · exact absurd ((hFoot0Cur a h0).trans_le (hInv.hLo.trans hRetLo)) (by omega)
              · omega
            · simp only [tok', Function.update_of_ne hrc]; intro hf
              have hLoS := hInv.hLo
              by_cases hrt : r < t
              · rcases (hTokRep r hr).2.1 hrt a hf with h0 | ⟨_, hhi⟩
                · exact absurd ((hCores r hr).2.2.2.2.2.2.1 a h0) (by omega)
                · omega
              · rw [(hTokRep r hr).2.2 (by omega)] at hf
                exact absurd ((hCores r hr).2.2.2.2.2.2.1 a hf) (by omega)
        · obtain ⟨vc, ec, hDGt, hLoT, hHiT, hDisjT⟩ := hForests t (by omega)
          have hLoS := hInv.hLo
          have hPtrEq' : sNext.mem (dstPtrs + t) = s.mem (dstPtrs + t) :=
            (h9Eq4 _ (by omega) (by omega)).trans (hFr4 _ (by omega) (hDstNotF t (by omega)))
          refine ⟨vc, ec, hPtrEq'.symm ▸ dynGraphAt_of_agree hDGt (fun a ha1 ha2 =>
              (h9Eq4 a (by omega) (by omega)).trans
                (hFr4 a (by omega) (fun hf => hDisjT cur hlt a ha1 ha2 (hTokCurEq.symm ▸ hf)))),
            by rw [hPtrEq']; exact hLoT,
            by rw [hPtrEq']; simp only [sNext, s9, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19),
              Function.update_self]; dsimp [newHeap]; omega,
            fun r hr a ha1 ha2 => by
              rw [hPtrEq'] at ha1 ha2
              by_cases hrc : r = cur
              · subst hrc; simp only [tok', Function.update_self]; intro hf
                rcases hFoot4 a hf with h0 | ⟨hlo, _⟩
                · exact hDisjT r hlt a ha1 ha2 (hTokCurEq.symm ▸ h0)
                · omega
              · simp only [tok', Function.update_of_ne hrc]; exact hDisjT r hr a ha1 ha2⟩
    obtain ⟨out, cRest, potEnd, rRest, hEnd, hcRest⟩ := ih (cur + 1) sNext potNext (by omega) hInvNext
    have rCond : Runs w p ω (forUp 19 (.reg 75) body) s .normal out
        (3 + ((5 + (5 + (7 + (cOp2 + (5 + (2 + (cCopy + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 4 + 1) + cRest + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, sNext, _, cRest,
        by simp [Expr.eval, BinOp.eval, hInv.r19, hInv.r75, hlt, hw1], by omega,
        runs_seq_iff.mpr (Or.inr ⟨s9, _, 4, rBody, rInc, rfl⟩), rRest,
        by simp [Expr.size]⟩))
    refine ⟨out, _, potEnd, rCond, hEnd, ?_⟩
    have hMulD : (rem + 1) * (P.readout + 17 * dgCap + 100) =
        rem * (P.readout + 17 * dgCap + 100) + (P.readout + 17 * dgCap + 100) := Nat.succ_mul _ _
    omega

end MinCostFlow.MinRatio
