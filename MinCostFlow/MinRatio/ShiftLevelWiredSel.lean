module

public import MinCostFlow.MinRatio.OrdSelSpecs
public import MinCostFlow.MinRatio.ShiftLevelWired
public import MinCostFlow.MinRatio.ShiftTermFacts
public import MinCostFlow.MinRatio.ShiftDeepModelFacts
import WordRAM.Tactic

/-!
# Select-aware wired level shift (`ShiftLevelWiredSel`)

Proves `shiftLevelStepSpecWKFBLSel_wired`: `shiftLevelWiredBody` implements
`ShiftLevelStepSpecWKFBLSel` from `ShiftTermChainSyncSpecWExtKFBLSel` (at
`lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`) and `ShiftDeepChainSyncSpecWExtKFBLSel`.
Threads `SolverLevelCapsInv`, `SolverSelectInv`, `sg.reembPot = chainReembPot pot`, footprint
`Rrep.foot ∨ sg.owned`, and combined potential `Rrep.phi + K * sg.reembPot`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program MinCostFlow.Bundle

/-- Discharges `ShiftLevelStepSpecWKFBLSel` for `shiftLevelWiredBody` from
`ShiftTermChainSyncSpecWExtKFBLSel` and `ShiftDeepChainSyncSpecWExtKFBLSel`. -/
theorem shiftLevelStepSpecWKFBLSel_wired
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap dMul kOff K E pLast slot shiftLevelProc shiftTermChainProc shiftDeepChainProc
      termSpace termFixed deepSpace deepFixed toolMul treeMul : ℕ}
    {cfg : Alg2Config} {G : MGraph} {pot : cfg.T.State → ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hAt : p.procs[shiftLevelProc]? =
      some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc))
    (hV : cfg.ValidOrdNoHidden)
    (hTerm : ShiftTermChainSyncSpecWExtKFBLSel w L P m V psi k epsExp drainUnit capExp limbMul
      capLimit (2 * levelM cfg.TP cfg.P cfg.P.d) vCap eCap dMul kOff K E pLast slot cfg G pot DeepInv
      Rcore p shiftTermChainProc termSpace termFixed toolMul treeMul)
    (hDeep : ShiftDeepChainSyncSpecWExtKFBLSel w L P m V psi k epsExp drainUnit capExp limbMul
      capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap dMul kOff K E pLast slot cfg G pot
      DeepInv Rcore p shiftDeepChainProc deepSpace deepFixed toolMul treeMul)
    (hw17 : 17 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) :
    ShiftLevelStepSpecWKFBLSel w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap dMul kOff K E pLast slot cfg G pot DeepInv
      Rcore p shiftLevelProc (max termSpace deepSpace)
      (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220) toolMul treeMul := by
  obtain ⟨bTerm, hbTerm, hTermRun⟩ := hTerm
  obtain ⟨bDeep, hbDeep, hDeepRun⟩ := hDeep
  refine ⟨shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc, hAt, ?_⟩
  intro root heap pos i ω mem model tok sg B R
  dsimp only
  intro hAcc hBranchLt hBrAll hQuotaW hPassW hrep hMeta hCaps hLay hSel hPot hReg hLoopInv hDeepInv
    hDeepModel hIntCap hFEdge hlogW hcapTree hnum hoff hbd hCap hbelow hz hroom
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hrep0 := hrep
  obtain ⟨hrootDir, _, _, hchainP, _, _, _, _, hsched, _, _, _, _, _, hcores, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, t4, t5, _⟩ := htags
  have hheapW : heap < 2 ^ w := by omega
  have hltH {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (Or.inl (hOwn a (ht ▸ hv))))
  have hrootW : root < 2 ^ w := lt_trans (hltH (t1 0 (by omega)) (by decide)) hheapW
  have hroot2W : root + 2 < 2 ^ w := lt_trans (hltH (t1 2 (by omega)) (by decide)) hheapW
  have hh11W : tok.handle + 11 < 2 ^ w := lt_trans (hltH (t2 11 (by omega)) (by decide)) hheapW
  have hh12W : tok.handle + 12 < 2 ^ w := lt_trans (hltH (t2 12 (by omega)) (by decide)) hheapW
  have hh17W : tok.handle + 18 < 2 ^ w := lt_trans (hltH (t4 0 (by omega)) (by decide)) hheapW
  have hbrEndW : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d < 2 ^ w := by
    have hlt := hltH (t4 (2 * cfg.P.d + 1) (by omega)) (by decide)
    have heq : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
    rw [heq]; exact lt_trans hlt hheapW
  have hlvEndW : tok.levelsEnd + 4 * (cfg.P.d + 1) < 2 ^ w :=
    lt_trans (hltH (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide)) hheapW
  have h4d1W : 4 * (cfg.P.d + 1) < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) hlvEndW
  have h3d1W : 3 * (cfg.P.d + 1) < 2 ^ w := by omega
  have hhandleEq : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hlevEq : mem (root + 2) = tok.levelsEnd := by simpa using hrootDir 2 (by simp)
  have hdEq : mem (tok.handle + 11) = cfg.P.d := by simpa [Nat.add_assoc] using hchainP 2 (by simp)
  have hkEq : mem (tok.handle + 12) = cfg.P.k := by simpa [Nat.add_assoc] using hchainP 3 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw12 : 12 < 2 ^ w := by omega
  have hiLt : i.val < cfg.P.d + 1 := i.isLt
  have hiLe : i.val ≤ cfg.P.d := Nat.lt_succ_iff.mp hiLt
  -- Prefix: load parameters and run `recordAcceptedShift`
  let s0 := startState [root, i.val, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 20 root }
  let s2 : State := { s1 with regs := Function.update s1.regs 21 i.val }
  let s3 : State := { s2 with regs := Function.update s2.regs 22 heap }
  let s4 : State := { s3 with regs := Function.update s3.regs 23 tok.handle }
  let s5 : State := { s4 with regs := Function.update s4.regs 24 tok.levelsEnd }
  let s6 : State := { s5 with regs := Function.update s5.regs 25 cfg.P.d }
  let s7 : State := { s6 with regs := Function.update s6.regs 26 cfg.P.k }
  let s8 : State := { s7 with regs := Function.update s7.regs 27 (cfg.P.d + 1) }
  let s9 : State := { s8 with regs := Function.update s8.regs 0 (tok.levelsEnd + (cfg.P.d + 1)) }
  let s10 : State := { s9 with regs := Function.update s9.regs 1 i.val }
  have r1 : Runs w p ω (.assign 20 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 21 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨i.val, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 22 (.reg 2)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 23 (.load (.reg 20))) s3 .normal s4 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s3, s2, s1, s0, startState, hhandleEq], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 20) (.const 2)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, show 2 < 2 ^ w by omega, hroot2W, hlevEq],
      rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 23) (.const 11)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨cfg.P.d, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, show 11 < 2 ^ w by omega, hh11W, hdEq],
      rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 26 (.load (.bin .add (.reg 23) (.const 12)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨cfg.P.k, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState, hw12, hh12W, hkEq], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 27 (.bin .add (.reg 25) (.const 1))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨cfg.P.d + 1, by simp [Expr.eval, BinOp.eval, s7, s6, hw1, hdW], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 0 (.bin .add (.reg 24) (.reg 27))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd + (cfg.P.d + 1), by
      simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, show tok.levelsEnd + (cfg.P.d + 1) < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 1 (.reg 21)) s9 .normal s10 2 :=
    runs_assign_iff.mpr ⟨i.val, by simp [Expr.eval, s9, s8, s7, s6, s5, s4, s3, s2], rfl, rfl, rfl⟩
  have hpsiNN : 0 ≤ alg2PsiGame cfg.Ψ cfg.P.M₀ :=
    le_trans (by norm_num) (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀)
  have hshiftLtQuota : model.chain.shiftCount i.val <
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val :=
    (shiftQuotaWord_lt_iff cfg.P _ model.chain.rebuildCount i.val _ hpsiNN).mpr hAcc
  obtain ⟨s11, r11, hs11Mem, hs11Regs, _⟩ :=
    recordAcceptedShift_runs (w := w) (base := tok.levelsEnd + (cfg.P.d + 1)) (level := i.val)
      (count := model.chain.shiftCount i.val)
      (quota := shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val)
      (p := p) (st := s10) (ω := ω)
      (by simp [s10, s9]) (by simp [s10])
      (by simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState]; exact hsched.2.1 i.val hiLe)
      (by omega) hshiftLtQuota hQuotaW
  have hs11Tag (a : ℕ) (hne5 : tok.tag a ≠ 5) : s11.mem a = mem a := by
    rw [hs11Mem]
    have hne : a ≠ tok.levelsEnd + (cfg.P.d + 1) + i.val := by
      intro heq; apply hne5; rw [heq, Nat.add_assoc]; exact t5 (cfg.P.d + 1 + i.val) (by omega)
    rw [Function.update_of_ne hne]; rfl
  have hrChain {tail : Stmt} {res : Outcome} {endSt : State} {cTail : ℕ}
      (htail : Runs w p ω tail s11 res endSt cTail) :
      Runs w p ω
        (.assign 20 (.reg 0) ;; .assign 21 (.reg 1) ;; .assign 22 (.reg 2) ;;
         .assign 23 (.load (.reg 20)) ;; .assign 24 (.load (.bin .add (.reg 20) (.const 2))) ;;
         .assign 25 (.load (.bin .add (.reg 23) (.const 11))) ;;
         .assign 26 (.load (.bin .add (.reg 23) (.const 12))) ;;
         .assign 27 (.bin .add (.reg 25) (.const 1)) ;;
         .assign 0 (.bin .add (.reg 24) (.reg 27)) ;; .assign 1 (.reg 21) ;;
         recordAcceptedShift ;; tail)
        s0 res endSt (cTail + 55) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, cTail + 52, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, cTail + 49, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, cTail + 46, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 3, cTail + 42, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, cTail + 36, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, cTail + 30, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, cTail + 24, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 4, cTail + 19, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 4, cTail + 14, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 2, cTail + 11, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 10, cTail, r11, htail, by omega⟩), by omega⟩),
    by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  have hs11_20 : s11.regs 20 = root := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  have hs11_21 : s11.regs 21 = i.val := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4, s3, s2]
  have hs11_22 : s11.regs 22 = heap := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4, s3]
  have hs11_23 : s11.regs 23 = tok.handle := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4]
  have hs11_24 : s11.regs 24 = tok.levelsEnd := by simp [hs11Regs, s10, s9, s8, s7, s6, s5]
  have hs11_25 : s11.regs 25 = cfg.P.d := by simp [hs11Regs, s10, s9, s8, s7, s6]
  have hs11_26 : s11.regs 26 = cfg.P.k := by simp [hs11Regs, s10, s9, s8, s7]
  have hs11_27 : s11.regs 27 = cfg.P.d + 1 := by simp [hs11Regs, s10, s9, s8]
  by_cases hiD : i.val < cfg.P.d
  · -- Non-terminal branch (`i < cfg.P.d`)
    have hcond1 : (Expr.bin .lt (.reg 21) (.reg 25)).eval w s11 = some 1 := by
      simp [Expr.eval, BinOp.eval, hs11_21, hs11_25, hiD, hw1]
    have hcurB : model.chain.bran i.val < cfg.P.k := by simpa [hiD] using hBranchLt
    have hbrMem : s11.mem (tok.handle + 18 + (cfg.P.d + 1) + i.val) = model.chain.bran i.val := by
      have hne5 : tok.tag (tok.handle + 18 + (cfg.P.d + 1) + i.val) ≠ 5 := by
        have h4 := t4 (cfg.P.d + 1 + i.val) (by omega)
        rw [← Nat.add_assoc] at h4; rw [h4]; decide
      exact (hs11Tag _ hne5).trans (hcores i.val hiD).2.1
    let wrapped : Bool := decide ((model.chain.bran i.val + 1) % cfg.P.k = 0)
    let t1St : State := { s11 with regs := Function.update s11.regs 28 (tok.handle + 18 + (cfg.P.d + 1)) }
    let t2St : State := { t1St with regs := Function.update t1St.regs 29 (model.chain.bran i.val) }
    let t3St : State := { t2St with regs := Function.update t2St.regs 3 (if wrapped then 1 else 0) }
    let t4St : State := { t3St with regs := Function.update t3St.regs 0 tok.levelsEnd }
    let t5St : State := { t4St with regs := Function.update t4St.regs 1 i.val }
    let t6St : State := { t5St with regs := Function.update t5St.regs 2 (cfg.P.d + 1) }
    have rt1 : Runs w p ω (.assign 28 (.bin .add (.bin .add (.reg 23) (.const 18)) (.reg 27)))
        s11 .normal t1St 6 :=
      runs_assign_iff.mpr ⟨tok.handle + 18 + (cfg.P.d + 1), by
        simp [Expr.eval, BinOp.eval, hs11_23, hs11_27, show 18 < 2 ^ w by omega, hh17W,
          show tok.handle + 18 + (cfg.P.d + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rt2 : Runs w p ω (.assign 29 (.load (.bin .add (.reg 28) (.reg 21))))
        t1St .normal t2St 5 :=
      runs_assign_iff.mpr ⟨model.chain.bran i.val, by
        simp [Expr.eval, BinOp.eval, t1St, hs11_21,
          show tok.handle + 18 + (cfg.P.d + 1) + i.val < 2 ^ w by omega, hbrMem], rfl, rfl, rfl⟩
    have hmodW : (model.chain.bran i.val + 1) % cfg.P.k < 2 ^ w :=
      lt_trans (Nat.mod_lt _ (by omega)) hkW
    have rt3 : Runs w p ω (.assign 3 (.bin .eq (.bin .mod (.bin .add (.reg 29) (.const 1)) (.reg 26)) (.const 0)))
        t2St .normal t3St 8 :=
      runs_assign_iff.mpr ⟨if wrapped then 1 else 0, by
        by_cases h0 : (model.chain.bran i.val + 1) % cfg.P.k = 0 <;>
          simp [Expr.eval, BinOp.eval, t2St, t1St, hs11_26, hw1,
            show model.chain.bran i.val + 1 < 2 ^ w by omega,
            hmodW, show 0 < 2 ^ w by omega, wrapped, h0], rfl, rfl, rfl⟩
    have rt4 : Runs w p ω (.assign 0 (.reg 24)) t3St .normal t4St 2 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd, by simp [Expr.eval, t3St, t2St, t1St, hs11_24], rfl, rfl, rfl⟩
    have rt5 : Runs w p ω (.assign 1 (.reg 21)) t4St .normal t5St 2 :=
      runs_assign_iff.mpr ⟨i.val, by simp [Expr.eval, t4St, t3St, t2St, t1St, hs11_21], rfl, rfl, rfl⟩
    have rt6 : Runs w p ω (.assign 2 (.reg 27)) t5St .normal t6St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.d + 1, by simp [Expr.eval, t5St, t4St, t3St, t2St, t1St, hs11_27], rfl, rfl, rfl⟩
    have hpassTable6 : ∀ j : Fin (cfg.P.d + 1), t6St.mem (tok.levelsEnd + j.val) = model.passes j := by
      intro j
      change s11.mem (tok.levelsEnd + j.val) = model.passes j
      rw [hs11Mem, Function.update_of_ne (by have := j.isLt; omega)]
      exact hsched.1 j
    obtain ⟨t7St, cPass, rt7, hcPass, _, ht7Frame, ht7Passes⟩ :=
      advanceShiftPasses_table_runs (w := w) (base := tok.levelsEnd) (levels := cfg.P.d + 1) (p := p)
        (st := t6St) (ω := ω) i model.passes wrapped
        (by simp [t6St, t5St, t4St]) (by simp [t6St, t5St]) (by simp [t6St])
        (by simp [t6St, t5St, t4St, t3St]) hpassTable6 (by omega) hw1 (fun _ => hPassW)
    have ht7_reg (r : ℕ) (hr : 20 ≤ r) : t7St.regs r = t6St.regs r :=
      runs_preserves_above hr (by rfl) rt7
    let t8St : State := { t7St with mem := Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 }
    let t9St : State := { t8St with regs := Function.update t8St.regs 0 (tok.levelsEnd + 3 * (cfg.P.d + 1)) }
    let t10St : State := { t9St with regs := Function.update t9St.regs 1 (i.val + 1) }
    let t11St : State := { t10St with regs := Function.update t10St.regs 2 cfg.P.d }
    have rt8 : Runs w p ω (.store (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 27))) (.const 0))
        t7St .normal t8St 7 :=
      runs_store_iff.mpr ⟨tok.levelsEnd + 4 * (cfg.P.d + 1), 0, by
        simp [Expr.eval, BinOp.eval, ht7_reg 24 (by decide), ht7_reg 27 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_24, hs11_27, hw4, h4d1W, hlvEndW],
        by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rt9 : Runs w p ω (.assign 0 (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 27))))
        t8St .normal t9St 6 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd + 3 * (cfg.P.d + 1), by
        simp [Expr.eval, BinOp.eval, t8St, ht7_reg 24 (by decide), ht7_reg 27 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_24, hs11_27, show 3 < 2 ^ w by omega,
          h3d1W, show tok.levelsEnd + 3 * (cfg.P.d + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rt10 : Runs w p ω (.assign 1 (.bin .add (.reg 21) (.const 1))) t9St .normal t10St 4 :=
      runs_assign_iff.mpr ⟨i.val + 1, by
        simp [Expr.eval, BinOp.eval, t9St, t8St, ht7_reg 21 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_21, hw1, show i.val + 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have rt11 : Runs w p ω (.assign 2 (.reg 25)) t10St .normal t11St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.d, by
        simp [Expr.eval, t10St, t9St, t8St, ht7_reg 25 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_25], rfl, rfl, rfl⟩
    obtain ⟨t12St, cUpd, rt12, hcUpd, ht12Mem, ht12Regs, _⟩ :=
      resetPassSuffix_runs (w := w) (base := tok.levelsEnd + 3 * (cfg.P.d + 1)) (first := i.val + 1)
        (stop := cfg.P.d) (p := p) (st := t11St) (ω := ω)
        (by simp [t11St, t10St, t9St]) (by simp [t11St, t10St]) (by simp [t11St])
        (by omega) (by omega) hw1
    have ht12Tag (a : ℕ) (hne5 : tok.tag a ≠ 5) : t12St.mem a = mem a := by
      have hnot5 : ¬ (tok.levelsEnd ≤ a ∧ a < tok.levelsEnd + (4 * (cfg.P.d + 1) + 1)) := by
        intro hIn
        apply hne5
        have hsub : tok.levelsEnd + (a - tok.levelsEnd) = a := Nat.add_sub_of_le hIn.1
        rw [← hsub]; exact t5 (a - tok.levelsEnd) (by omega)
      rw [ht12Mem a, ite_eq_right (by omega)]
      change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 a = mem a
      rw [Function.update_of_ne (by omega)]
      rw [ht7Frame a (by omega)]
      exact hs11Tag a hne5
    have ht12Sched : SolverScheduleAt t12St.mem tok.levelsEnd (alg2LoopShiftStep cfg model i) := by
      refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
      · have hjLt : j.val < cfg.P.d + 1 := j.isLt
        rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 (tok.levelsEnd + j.val) = _
        rw [Function.update_of_ne (by omega), ht7Passes j]
        simp [alg2LoopShiftStep, hiD, wrapped]
      · rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
        rw [Function.update_of_ne (by omega), ht7Frame _ (by omega)]
        change s11.mem (tok.levelsEnd + (cfg.P.d + 1) + j) = _
        rw [hs11Mem, alg2LoopShiftStep, ordAlgorithm1_shift_shiftCount model.chain hiLe]
        by_cases hji : j = i.val
        · subst hji; simp
        · rw [Function.update_of_ne (by omega), ite_eq_right hji]; exact hsched.2.1 j hj
      · rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
        rw [Function.update_of_ne (by omega), ht7Frame _ (by omega)]
        change s11.mem (tok.levelsEnd + 2 * (cfg.P.d + 1) + j) = _
        rw [hs11Mem, Function.update_of_ne (by omega), alg2LoopShiftStep, ordAlgorithm1_shift_rebuildCount]
        exact hsched.2.2.1 j hj
      · rw [ht12Mem, alg2LoopShiftStep, ordAlgorithm1_shift_updCount_lt model.chain hiD]
        have hiff : (tok.levelsEnd + 3 * (cfg.P.d + 1) + (i.val + 1) ≤ tok.levelsEnd + 3 * (cfg.P.d + 1) + j ∧
            tok.levelsEnd + 3 * (cfg.P.d + 1) + j < tok.levelsEnd + 3 * (cfg.P.d + 1) + cfg.P.d) ↔
            (i.val + 1 ≤ j ∧ j < cfg.P.d) := by omega
        simp only [hiff]
        split_ifs with hIn
        · rfl
        · change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
          rw [Function.update_of_ne (by omega), ht7Frame _ (by omega)]
          change s11.mem (tok.levelsEnd + 3 * (cfg.P.d + 1) + j) = _
          rw [hs11Mem, Function.update_of_ne (by omega)]
          exact hsched.2.2.2.1 j hj
      · rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
        simp [alg2LoopShiftStep, hiD]
    have ht12Zero : ZeroFrom t12St.mem heap := fun a ha => by
      have hne5 : tok.tag a ≠ 5 := fun h5 => Nat.not_lt_of_ge ha (hltH h5 (by decide))
      exact (ht12Tag a hne5).trans (hz a ha)
    have hK : ShiftDeepModelInvKFBL model i := shiftDeepModelInvKFBL_of_loopInv hV hLoopInv hiD
    have hSum := (shiftDeep_forestEdgeSum_le_two_G0_n hV hLoopInv hiD).1.trans hFEdge
    obtain ⟨nextHeap, cDeep, out, tok', sg', hrDeep, hloD, hhiD, hlevD, hintCapD, htblD, hrcapD,
        hrepD, hMetaD, hCapsD, hLayD, hSelD, hPotD, hRegD, hnumD, hoffD, hbdD, hzD, hfrD, hftD, hcD⟩ :=
      hDeepRun root heap t12St.pos i ω mem t12St.mem model tok sg B R hiD hrep0 hMeta hCaps hLay hSel
        hPot hReg hLoopInv hDeepInv ht12Tag ht12Sched hnum hoff hbd hCap hBrAll (hDeepModel hiD) hK
        hIntCap hSum hlogW hcapTree hbelow ht12Zero (by omega)
    let t13St : State := { regs := Function.update t12St.regs 30 nextHeap, mem := out.mem, pos := out.pos }
    have rt13 : Runs w p ω (.call 30 shiftDeepChainProc [.reg 20, .reg 21, .reg 22])
        t12St .normal t13St (cDeep + 4) :=
      runs_call_iff.mpr ⟨[root, i.val, heap], bDeep, .returned nextHeap, out, cDeep, by
        simp [evalArgs, Expr.eval, ht12Regs 20 (by decide), ht12Regs 21 (by decide), ht12Regs 22 (by decide),
          t11St, t10St, t9St, t8St, ht7_reg 20 (by decide), ht7_reg 21 (by decide), ht7_reg 22 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_20, hs11_21, hs11_22],
        hbDeep, hrDeep, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have rt14 : Runs w p ω (.ret (.reg 30)) t13St (.returned nextHeap) t13St 2 :=
      runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, t13St], rfl, rfl, rfl⟩
    have hrThen : Runs w p ω _ s11 (.returned nextHeap) t13St
        (6 + (5 + (8 + (2 + (2 + (2 + (cPass + (7 + (6 + (4 + (2 + (cUpd + ((cDeep + 4) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨t1St, 6, _, rt1,
      runs_seq_iff.mpr (Or.inr ⟨t2St, 5, _, rt2,
      runs_seq_iff.mpr (Or.inr ⟨t3St, 8, _, rt3,
      runs_seq_iff.mpr (Or.inr ⟨t4St, 2, _, rt4,
      runs_seq_iff.mpr (Or.inr ⟨t5St, 2, _, rt5,
      runs_seq_iff.mpr (Or.inr ⟨t6St, 2, _, rt6,
      runs_seq_iff.mpr (Or.inr ⟨t7St, cPass, _, rt7,
      runs_seq_iff.mpr (Or.inr ⟨t8St, 7, _, rt8,
      runs_seq_iff.mpr (Or.inr ⟨t9St, 6, _, rt9,
      runs_seq_iff.mpr (Or.inr ⟨t10St, 4, _, rt10,
      runs_seq_iff.mpr (Or.inr ⟨t11St, 2, _, rt11,
      runs_seq_iff.mpr (Or.inr ⟨t12St, cUpd, _, rt12,
      runs_seq_iff.mpr (Or.inr ⟨t13St, cDeep + 4, 2, rt13, rt14, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨nextHeap, _, t13St, tok', sg',
      hrChain (runs_cond_iff.mpr ⟨1, _, hcond1,
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrThen, rfl⟩),
      hloD, le_trans hhiD (Nat.add_le_add_left (le_max_right _ _) _), hlevD, hintCapD, htblD, hrcapD,
      hrepD, hMetaD, hCapsD, hLayD, hSelD, hPotD, hRegD, hnumD, hoffD, hbdD, hzD,
      fun a ha hnot => (hfrD a ha hnot).trans (ht12Tag a (fun h5 => hnot (Or.inl (Or.inl (hOwn a (h5 ▸ by decide)))))),
      hftD, ?_⟩
    dsimp only [t13St]
    simp only [Expr.size]
    have := le_max_right termFixed deepFixed
    omega
  · -- Terminal branch (`i = cfg.P.d`)
    have hiEqD : i = Fin.last cfg.P.d := Fin.ext (by simp only [Fin.val_last]; omega)
    have hcond0 : (Expr.bin .lt (.reg 21) (.reg 25)).eval w s11 = some 0 := by
      simp [Expr.eval, BinOp.eval, hs11_21, hs11_25, hiD, show 0 < 2 ^ w by omega]
    have hbranD_lt : model.branD < cfg.P.k := by simpa [hiD] using hBranchLt
    let e1St : State := { s11 with regs := Function.update s11.regs 0 (tok.levelsEnd + 4 * (cfg.P.d + 1)) }
    let e2St : State := { e1St with regs := Function.update e1St.regs 1 cfg.P.k }
    let e3St : State := { e2St with regs := Function.update e2St.regs 4 tok.levelsEnd }
    let e4St : State := { e3St with regs := Function.update e3St.regs 5 cfg.P.d }
    have re1 : Runs w p ω (.assign 0 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 27))))
        s11 .normal e1St 6 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd + 4 * (cfg.P.d + 1), by
        simp [Expr.eval, BinOp.eval, hs11_24, hs11_27, hw4, h4d1W, hlvEndW], rfl, rfl, rfl⟩
    have re2 : Runs w p ω (.assign 1 (.reg 26)) e1St .normal e2St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.k, by simp [Expr.eval, e1St, hs11_26], rfl, rfl, rfl⟩
    have re3 : Runs w p ω (.assign 4 (.reg 24)) e2St .normal e3St 2 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd, by simp [Expr.eval, e2St, e1St, hs11_24], rfl, rfl, rfl⟩
    have re4 : Runs w p ω (.assign 5 (.reg 25)) e3St .normal e4St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.d, by simp [Expr.eval, e3St, e2St, e1St, hs11_25], rfl, rfl, rfl⟩
    have he4BranD : e4St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) = model.branD := by
      change s11.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) = model.branD
      rw [hs11Mem, Function.update_of_ne (by omega)]; exact hsched.2.2.2.2
    have he4Pass : e4St.mem (tok.levelsEnd + cfg.P.d) = model.passes (Fin.last cfg.P.d) := by
      change s11.mem (tok.levelsEnd + cfg.P.d) = model.passes (Fin.last cfg.P.d)
      rw [hs11Mem, Function.update_of_ne (by omega)]; exact hsched.1 (Fin.last cfg.P.d)
    obtain ⟨e5St, cTermSched, re5, hcTermSched, _, he5Mem⟩ :=
      shiftTerminalSchedule_runs (w := w) (addr := tok.levelsEnd + 4 * (cfg.P.d + 1)) (branch := model.branD)
        (k := cfg.P.k) (base := tok.levelsEnd) (d := cfg.P.d) (count := model.passes (Fin.last cfg.P.d))
        (p := p) (st := e4St) (ω := ω)
        (by simp [e4St, e3St, e2St, e1St]) (by simp [e4St, e3St, e2St])
        he4BranD hbranD_lt hkW (by simp [e4St, e3St]) (by simp [e4St]) he4Pass
        (by omega) (by omega) (fun _ => hiEqD ▸ hPassW)
    have he5_reg (r : ℕ) (hr : 20 ≤ r) : e5St.regs r = e4St.regs r :=
      runs_preserves_above hr (by rfl) re5
    have he5Tag (a : ℕ) (hne5 : tok.tag a ≠ 5) : e5St.mem a = mem a := by
      have hnot5 : ¬ (tok.levelsEnd ≤ a ∧ a < tok.levelsEnd + (4 * (cfg.P.d + 1) + 1)) := by
        intro hIn
        apply hne5
        have hsub : tok.levelsEnd + (a - tok.levelsEnd) = a := Nat.add_sub_of_le hIn.1
        rw [← hsub]; exact t5 (a - tok.levelsEnd) (by omega)
      rw [he5Mem a, ite_eq_right (by omega)]
      rw [Function.update_of_ne (by omega)]
      exact hs11Tag a hne5
    have he5Sched : SolverScheduleAt e5St.mem tok.levelsEnd (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)) := by
      refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
      · rw [he5Mem]
        have hneBr : tok.levelsEnd + j.val ≠ tok.levelsEnd + 4 * (cfg.P.d + 1) := by have := j.isLt; omega
        rw [Function.update_of_ne hneBr]
        have hjNotGt : ¬ Fin.last cfg.P.d < j := Fin.not_lt.mpr (Fin.le_last j)
        change _ = if Fin.last cfg.P.d < j then 0 else if j = Fin.last cfg.P.d then _ else model.passes j
        rw [ite_eq_right hjNotGt]
        by_cases hjd : j = Fin.last cfg.P.d
        · subst hjd
          simp only [Fin.val_last, true_and, ↓reduceIte, Nat.lt_irrefl]
          split_ifs with hw
          · rfl
          · exact he4Pass
        · have hneVal : j.val ≠ cfg.P.d := fun h => hjd (Fin.ext h)
          rw [ite_eq_right (by omega), ite_eq_right hjd]
          change s11.mem (tok.levelsEnd + j.val) = _
          rw [hs11Mem, Function.update_of_ne (by omega)]; exact hsched.1 j
      · rw [he5Mem, ite_eq_right (by omega), Function.update_of_ne (by omega)]
        change s11.mem (tok.levelsEnd + (cfg.P.d + 1) + j) = _
        rw [hs11Mem, alg2LoopShiftStep, Fin.val_last, ordAlgorithm1_shift_shiftCount model.chain le_rfl]
        have hiValD : i.val = cfg.P.d := congrArg Fin.val hiEqD
        rw [hiValD]
        by_cases hjd : j = cfg.P.d
        · subst hjd; simp
        · rw [Function.update_of_ne (by omega), ite_eq_right hjd]; exact hsched.2.1 j hj
      · rw [he5Mem, ite_eq_right (by omega), Function.update_of_ne (by omega)]
        change s11.mem (tok.levelsEnd + 2 * (cfg.P.d + 1) + j) = _
        rw [hs11Mem, Function.update_of_ne (by omega), alg2LoopShiftStep, ordAlgorithm1_shift_rebuildCount]
        exact hsched.2.2.1 j hj
      · rw [he5Mem, ite_eq_right (by omega), Function.update_of_ne (by omega)]
        change s11.mem (tok.levelsEnd + 3 * (cfg.P.d + 1) + j) = _
        rw [hs11Mem, Function.update_of_ne (by omega), alg2LoopShiftStep, Fin.val_last, ordAlgorithm1_shift_updCount_eq]
        exact hsched.2.2.2.1 j hj
      · rw [he5Mem, ite_eq_right (by omega), Function.update_self]
        simp [alg2LoopShiftStep]
    have he5Zero : ZeroFrom e5St.mem heap := fun a ha => by
      have hne5 : tok.tag a ≠ 5 := fun h5 => Nat.not_lt_of_ge ha (hltH h5 (by decide))
      exact (he5Tag a hne5).trans (hz a ha)
    obtain ⟨f1, f2, f5, f6, f7, f8, f9⟩ := shiftTerm_reached_facts_1_to_9 hV hLoopInv hrep0
      (fun a ha => hbelow a (Or.inl ha)) hheapW
    obtain ⟨nextHeap, cTerm, out, tok', sg', hrTerm, hloT, hhiT, hlevT, hintCapT, htblT, hrcapT,
        hrepT, hMetaT, hCapsT, hLayT, hSelT, hPotT, hRegT, hnumT, hoffT, hbdT, hzT, hfrT, hftT, hcT⟩ :=
      hTermRun root heap e5St.pos ω mem e5St.mem model tok sg B R hrep0 hMeta hCaps hLay hSel hPot hReg
        hLoopInv hDeepInv he5Tag he5Sched hnum hoff hbd hCap hBrAll f1 f2 hlogW hcapTree
        f5 f6 f7 f8 f9 hbelow he5Zero (by omega)
    let e6St : State := { regs := Function.update e5St.regs 30 nextHeap, mem := out.mem, pos := out.pos }
    have re6 : Runs w p ω (.call 30 shiftTermChainProc [.reg 20, .reg 22])
        e5St .normal e6St (cTerm + 3) :=
      runs_call_iff.mpr ⟨[root, heap], bTerm, .returned nextHeap, out, cTerm, by
        simp [evalArgs, Expr.eval, he5_reg 20 (by decide), he5_reg 22 (by decide),
          e4St, e3St, e2St, e1St, hs11_20, hs11_22],
        hbTerm, hrTerm, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have re7 : Runs w p ω (.ret (.reg 30)) e6St (.returned nextHeap) e6St 2 :=
      runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, e6St], rfl, rfl, rfl⟩
    have hrElse : Runs w p ω _ s11 (.returned nextHeap) e6St
        (6 + (2 + (2 + (2 + (cTermSched + ((cTerm + 3) + 2 + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨e1St, 6, _, re1,
      runs_seq_iff.mpr (Or.inr ⟨e2St, 2, _, re2,
      runs_seq_iff.mpr (Or.inr ⟨e3St, 2, _, re3,
      runs_seq_iff.mpr (Or.inr ⟨e4St, 2, _, re4,
      runs_seq_iff.mpr (Or.inr ⟨e5St, cTermSched, _, re5,
      runs_seq_iff.mpr (Or.inr ⟨e6St, cTerm + 3, 2, re6, re7, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨nextHeap, _, e6St, tok', sg',
      hrChain (runs_cond_iff.mpr ⟨0, _, hcond0, by simp only [↓reduceIte]; exact hrElse, rfl⟩),
      hloT, le_trans hhiT (Nat.add_le_add_left (le_max_left _ _) _), hlevT, hintCapT, htblT, hrcapT,
      hiEqD.symm ▸ hrepT, hiEqD.symm ▸ hMetaT, hiEqD.symm ▸ hCapsT, hLayT, hiEqD.symm ▸ hSelT,
      hiEqD.symm ▸ hPotT, hiEqD.symm ▸ hRegT, hnumT, hiEqD.symm ▸ hoffT, hiEqD.symm ▸ hbdT, hzT,
      fun a ha hnot => (hfrT a ha hnot).trans (he5Tag a (fun h5 => hnot (Or.inl (Or.inl (hOwn a (h5 ▸ by decide)))))),
      hftT, ?_⟩
    subst hiEqD
    dsimp only [e6St]
    simp only [Expr.size]
    have := le_max_left termFixed deepFixed
    omega

end MinCostFlow.MinRatio
