module

public import MinCostFlow.MinRatio.WireChainCoreAccounts
public import MinCostFlow.MinRatio.SolverRep
import MinCostFlow.Num.AddCarry
import MinCostFlow.Num.NegateCarry
import WordRAM.Tactic

/-!
# Edge-account refresh execution (`WireChainCoreRefresh`)

Proves `wireRefreshOneAccountBody_runs`: executes `wireRefreshOneAccountBody` in `O(L^2)` steps
and `wireRefreshOneSpace L` words to compute `thrNew`, `acc = detOld + thrOld`,
`detNew = acc - thrNew`, canonical `PathEdgeAt` record `[1, 1, gNew, lNew, oldFlow, detNew]`,
and `isNegBit`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program MinCostFlow.IPM.Machine

/-! ### 1. First half of `wireRefreshOneAccountBody` (arithmetic + record header) -/

private def wireRefreshOnePart1Stmt (divide add sub negate : ℕ) : Stmt :=
  .call 8 divide [.reg 4, .reg 3, .reg 5, .reg 6, .reg 7] ;;
  .assign 9 (.bin .sub (.reg 8) (.reg 5)) ;;
  .call 10 negate [.reg 9, .reg 5, .reg 8] ;;
  .assign 11 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 3) (.reg 5))) ;;
  .call 12 add [.reg 11, .reg 1, .reg 5, .reg 10] ;;
  .call 13 sub [.reg 10, .reg 8, .reg 5, .reg 12] ;;
  .assign 14 (.bin .add (.reg 12) (.reg 5)) ;;
  .store (.reg 13) (.const 1) ;;
  .store (.bin .add (.reg 13) (.const 1)) (.const 1)

private def wireRefreshOnePart2Stmt (copy isNeg : ℕ) : Stmt :=
  .call 15 copy [.reg 2, .bin .add (.reg 13) (.const 2), .reg 5] ;;
  .call 15 copy [.reg 3, .bin .add (.bin .add (.reg 13) (.const 2)) (.reg 5), .reg 5] ;;
  .call 15 copy [.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 5)),
    .bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 5)), .reg 5] ;;
  .call 15 copy [.reg 14, .bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 3) (.reg 5)), .reg 5] ;;
  .call 16 isNeg [.reg 14, .reg 5] ;;
  .assign 17 (.bin .add (.reg 13) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 5)))) ;;
  .store (.reg 17) (.reg 8) ;;
  .store (.bin .add (.reg 17) (.const 1)) (.reg 13) ;;
  .store (.bin .add (.reg 17) (.const 2)) (.reg 16) ;;
  .ret (.bin .add (.reg 17) (.const 3))

private theorem wireRefreshOnePart1_runs
    {w divide add sub negate oldRecPtr oldThrPtr gPtr lPtr negEpsPtr L P heap pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {oldVal : PathEdgeValue} {epsInt oldThr acc : ℤ} {lNewInt : ℕ}
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hadd : MeetsContract w p add (Num.addContract w 4))
    (hsub : MeetsContract w p sub (Num.subtractContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hLpos : 0 < L) (hlPos : 0 < lNewInt)
    (hRecLe : oldRecPtr + (2 + 4 * L) ≤ heap) (hThrLe : oldThrPtr + L ≤ heap)
    (hLLe : lPtr + L ≤ heap) (hEpsLe : negEpsPtr + L ≤ heap)
    (hOldRec : PathEdgeAt mem oldRecPtr 4 L (some oldVal))
    (hOldThr : PathIntAt mem oldThrPtr 4 L oldThr)
    (hOldDet : oldVal.detector = acc - oldThr)
    (hNegEps : PathIntAt mem negEpsPtr 4 L (-epsInt))
    (hLAt : PathIntAt mem lPtr 4 L (lNewInt : ℤ))
    (hFitNegThr : Num.Fits 4 L (-detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lNewInt : ℝ) / (2 : ℝ) ^ P)))
    (hFitPosThr : Num.Fits 4 L (detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lNewInt : ℝ) / (2 : ℝ) ^ P)))
    (hFitAcc : Num.Fits 4 L acc)
    (hFitDetNew : Num.Fits 4 L (acc - detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lNewInt : ℝ) / (2 : ℝ) ^ P)))
    (hz : ZeroFrom mem heap)
    (hRoom : heap + wireRefreshOneSpace L < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    let h1 := heap + Num.fixedDivideSpace L
    let h3 := h1 + 2 * L
    let h4 := h1 + 4 * L
    let thrNew := detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P) ((lNewInt : ℝ) / (2 : ℝ) ^ P)
    let s0 := startState [oldRecPtr, oldThrPtr, gPtr, lPtr, negEpsPtr, L, P, heap] mem pos
    ∃ s9 cA,
      Runs w p ω (wireRefreshOnePart1Stmt divide add sub negate) s0 .normal s9 cA ∧
      cA ≤ 2700 * L ^ 2 + 3000 * L + 860 ∧
      s9.regs 0 = oldRecPtr ∧ s9.regs 2 = gPtr ∧ s9.regs 3 = lPtr ∧ s9.regs 5 = L ∧
      s9.regs 8 = h1 ∧ s9.regs 13 = h4 ∧ s9.regs 14 = h3 + L ∧
      s9.mem h4 = 1 ∧ s9.mem (h4 + 1) = 1 ∧
      PathIntAt s9.mem h1 4 L thrNew ∧
      PathIntAt s9.mem (h3 + L) 4 L (acc - thrNew) ∧
      (∀ a < heap, s9.mem a = mem a) ∧
      (∀ a, h4 + 2 ≤ a → s9.mem a = 0) := by
  dsimp only
  set ε : ℝ := (epsInt : ℝ) / (2 : ℝ) ^ P
  set thrNew : ℤ := detectorThreshold P ε ((lNewInt : ℝ) / (2 : ℝ) ^ P)
  set h1 := heap + Num.fixedDivideSpace L
  set h2 := h1 + L
  set h3 := h2 + L
  set h4 := h3 + 2 * L
  have hh3 : h3 = h1 + 2 * L := by dsimp [h3, h2]; omega
  have hh4 : h4 = h1 + 4 * L := by dsimp [h4, h3, h2]; omega
  have hDivSp : 9 * L ≤ Num.fixedDivideSpace L := by unfold Num.fixedDivideSpace; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hLW : L < 2 ^ w := by unfold wireRefreshOneSpace at hRoom; omega
  have hRoom' : h4 + (2 + 4 * L) + 3 < 2 ^ w := by
    unfold wireRefreshOneSpace at hRoom; dsimp [h4, h3, h2, h1]; omega
  let s0 := startState [oldRecPtr, oldThrPtr, gPtr, lPtr, negEpsPtr, L, P, heap] mem pos
  have hDivC := detectorResidual_meetsContract (w := w) (h := 4) epsInt lNewInt hdiv
  obtain ⟨s1, c1, r1v, rc1, hp1, hr1_8, hs1Regs, hc1⟩ :=
    runs_call_of_meetsContract (r := 8) (args := [.reg 4, .reg 3, .reg 5, .reg 6, .reg 7])
      hDivC (st := s0) (vs := [negEpsPtr, lPtr, L, P, heap])
      (by simp [evalArgs, Expr.eval, s0, startState])
      (by simp [show negEpsPtr < 2 ^ w by omega, show lPtr < 2 ^ w by omega, hLW, hPword,
        show heap < 2 ^ w by omega])
      ⟨negEpsPtr, lPtr, L, P, heap, rfl, hPdiv, hEpsLe, hLLe, hlPos, hNegEps, hLAt, hFitNegThr, hz,
        by omega⟩ ω
  obtain ⟨_, _, _, _, _, hArgs1, hr1Eq, hNegThrAt, hFr1, hz1⟩ := hp1
  simp only [List.cons.injEq, and_true] at hArgs1
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hArgs1
  subst hr1Eq
  let s2 := { s1 with regs := Function.update s1.regs 9 (h1 - L) }
  have r2 : Runs w p ω (.assign 9 (.bin .sub (.reg 8) (.reg 5))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨h1 - L, by
      simp [Expr.eval, BinOp.eval, hr1_8, hs1Regs 5 (by decide), s0, startState, h1,
        show h1 - L < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨s3, c2, r2v, rc2, hp2, hr3_10, hs3Regs, hc2⟩ :=
    runs_call_of_meetsContract (r := 10) (args := [.reg 9, .reg 5, .reg 8])
      hneg (st := s2) (vs := [h1 - L, L, h1])
      (by simp [evalArgs, Expr.eval, s2, hr1_8, hs1Regs 5 (by decide), s0, startState, h1])
      (by simp [show h1 - L < 2 ^ w by omega, hLW, show h1 < 2 ^ w by omega])
      ⟨h1 - L, L, h1, rfl, ⟨⟨h1 - L, L, 1, h1, rfl, by omega, le_rfl, hNegThrAt.1⟩, hz1,
        by change h1 + L < 2 ^ w; omega⟩⟩ ω
  obtain ⟨hr2Eq, _, _, hFr2, hz2, hNegDig⟩ := hp2
  change r2v = h1 + L at hr2Eq; subst hr2Eq
  change ∀ x < h1, s3.mem x = s1.mem x at hFr2
  change ZeroFrom s3.mem (h1 + L) at hz2
  have hThrNewAt3 : PathIntAt s3.mem h1 4 L thrNew := by
    have hnv := Num.negateCarry_value_one hNegThrAt.1 hNegDig
    change Num.Valid s3.mem h1 4 L ∧ Num.intVal s3.mem h1 4 L = Num.wrap 4 L (-Num.intVal s1.mem (h1 - L) 4 L) at hnv
    refine ⟨hnv.1, ?_⟩
    rw [hnv.2, hNegThrAt.2, neg_neg, Num.wrap_of_fits hFitPosThr]
  let s4 := { s3 with regs := Function.update s3.regs 11 (oldRecPtr + 2 + 3 * L) }
  have r4 : Runs w p ω (.assign 11 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 3) (.reg 5))))
      s3 .normal s4 8 :=
    runs_assign_iff.mpr ⟨oldRecPtr + 2 + 3 * L, by
      simp [Expr.eval, BinOp.eval, hs3Regs 0 (by decide), hs3Regs 5 (by decide), s2,
        hs1Regs 0 (by decide), hs1Regs 5 (by decide), s0, startState, hw2, hw3,
        show oldRecPtr + 2 < 2 ^ w by omega, show 3 * L < 2 ^ w by omega,
        show oldRecPtr + 2 + 3 * L < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hFr30 (a : ℕ) (ha : a < heap) : s4.mem a = mem a :=
    (hFr2 a (lt_of_lt_of_le ha (by omega))).trans (hFr1 a ha)
  have hDetOldAt4 : PathIntAt s4.mem (oldRecPtr + 2 + 3 * L) 4 L oldVal.detector :=
    hOldRec.2.2.2.2.2.congr (fun j hj => hFr30 _ (by omega))
  have hOldThrAt4 : PathIntAt s4.mem oldThrPtr 4 L oldThr :=
    hOldThr.congr (fun j hj => hFr30 _ (by omega))
  obtain ⟨s5, c3, r3v, rc3, hp3, hr5_12, hs5Regs, hc3⟩ :=
    runs_call_of_meetsContract (r := 12) (args := [.reg 11, .reg 1, .reg 5, .reg 10])
      hadd (st := s4) (vs := [oldRecPtr + 2 + 3 * L, oldThrPtr, L, h2])
      (by simp [evalArgs, Expr.eval, s4, hs3Regs 1 (by decide), hs3Regs 5 (by decide), hr3_10,
        s2, hs1Regs 1 (by decide), hs1Regs 5 (by decide), s0, startState, h2])
      (by simp [show oldRecPtr + 2 + 3 * L < 2 ^ w by omega, show oldThrPtr < 2 ^ w by omega,
        hLW, show h2 < 2 ^ w by omega])
      ⟨oldRecPtr + 2 + 3 * L, oldThrPtr, L, h2, rfl,
        ⟨⟨oldRecPtr + 2 + 3 * L, oldThrPtr, L, 0, h2, rfl, by omega, by omega, by decide,
          hDetOldAt4.1, hOldThrAt4.1⟩, hz2, by change h2 + L < 2 ^ w; omega⟩⟩ ω
  obtain ⟨hr3Eq, _, _, hFr3, hz3, hAddDig⟩ := hp3
  change r3v = h2 + L at hr3Eq; subst hr3Eq
  change ∀ x < h2, s5.mem x = s4.mem x at hFr3
  change ZeroFrom s5.mem (h2 + L) at hz3
  have hAccAt5 : PathIntAt s5.mem h2 4 L acc := by
    have hav := Num.addCarry_value hAddDig
    change Num.Valid s5.mem h2 4 L ∧ Num.intVal s5.mem h2 4 L =
      Num.wrap 4 L (Num.intVal s4.mem (oldRecPtr + 2 + 3 * L) 4 L + Num.intVal s4.mem oldThrPtr 4 L + (0 : ℕ)) at hav
    refine ⟨hav.1, ?_⟩
    rw [hav.2, hDetOldAt4.2, hOldThrAt4.2, hOldDet]
    simp only [Int.natCast_zero, add_zero, sub_add_cancel, Num.wrap_of_fits hFitAcc]
  have hThrNewAt5 : PathIntAt s5.mem h1 4 L thrNew :=
    hThrNewAt3.congr (fun j hj => hFr3 _ (by omega))
  obtain ⟨s6, c4, r4v, rc4, hp4, hr6_13, hs6Regs, hc4⟩ :=
    runs_call_of_meetsContract (r := 13) (args := [.reg 10, .reg 8, .reg 5, .reg 12])
      hsub (st := s5) (vs := [h2, h1, L, h3])
      (by simp [evalArgs, Expr.eval, hs5Regs 10 (by decide), hs5Regs 8 (by decide),
        hs5Regs 5 (by decide), hr5_12, s4, hr3_10, hs3Regs 8 (by decide), hs3Regs 5 (by decide),
        s2, hr1_8, hs1Regs 5 (by decide), s0, startState, h1, h2, h3])
      (by simp [show h2 < 2 ^ w by omega, show h1 < 2 ^ w by omega, hLW, show h3 < 2 ^ w by omega])
      ⟨⟨h2, h1, L, h3, rfl, by omega, by omega, hAccAt5.1, hThrNewAt5.1⟩, hz3,
        by change h3 + 2 * L < 2 ^ w; omega⟩ ω
  obtain ⟨hr4Eq, _, _, hFr4, hz4, hDetV6, hDetInt6⟩ := hp4
  change r4v = h3 + 2 * L at hr4Eq; subst hr4Eq
  change ∀ x < h3, s6.mem x = s5.mem x at hFr4
  change ZeroFrom s6.mem (h3 + 2 * L) at hz4
  change Num.Valid s6.mem (h3 + L) 4 L at hDetV6
  change Num.intVal s6.mem (h3 + L) 4 L = Num.wrap 4 L (Num.intVal s5.mem h2 4 L - Num.intVal s5.mem h1 4 L) at hDetInt6
  have hDetNewAt6 : PathIntAt s6.mem (h3 + L) 4 L (acc - thrNew) := by
    refine ⟨hDetV6, ?_⟩
    rw [hDetInt6, hAccAt5.2, hThrNewAt5.2, Num.wrap_of_fits hFitDetNew]
  let s7 := { s6 with regs := Function.update s6.regs 14 (h3 + L) }
  let s8 := { s7 with mem := Function.update s7.mem h4 1 }
  let s9 := { s8 with mem := Function.update s8.mem (h4 + 1) 1 }
  have r7 : Runs w p ω (.assign 14 (.bin .add (.reg 12) (.reg 5))) s6 .normal s7 4 :=
    runs_assign_iff.mpr ⟨h3 + L, by
      simp [Expr.eval, BinOp.eval, hs6Regs 12 (by decide), hs6Regs 5 (by decide), hr5_12,
        hs5Regs 5 (by decide), s4, hs3Regs 5 (by decide), s2, hs1Regs 5 (by decide), s0, startState,
        h3, show h3 + L < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.store (.reg 13) (.const 1)) s7 .normal s8 3 :=
    runs_store_iff.mpr ⟨h4, 1, by simp [Expr.eval, s7, hr6_13, h4], by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.store (.bin .add (.reg 13) (.const 1)) (.const 1)) s8 .normal s9 5 :=
    runs_store_iff.mpr ⟨h4 + 1, 1, by
      simp [Expr.eval, BinOp.eval, s8, s7, hr6_13, hw1, h4, show h4 + 1 < 2 ^ w by omega],
      by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  have hs9Reg (r : ℕ) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12)
      (h13 : r ≠ 13) (h14 : r ≠ 14) : s9.regs r = s0.regs r := by
    simp only [s9, s8, s7, Function.update_of_ne h14, hs6Regs r h13, hs5Regs r h12,
      s4, Function.update_of_ne h11, hs3Regs r h10, s2, Function.update_of_ne h9, hs1Regs r h8]
  have hc1B : c1 ≤ 2700 * L ^ 2 + 2832 * L + 706 := by
    have harg1 : argsSize [Expr.reg 4, Expr.reg 3, Expr.reg 5, Expr.reg 6, Expr.reg 7] = 5 := rfl
    rw [harg1] at hc1
    change c1 ≤ 5 + (2700 * L ^ 2 + 2832 * L + 700) + 1 at hc1
    exact hc1.trans_eq (by ring)
  have hc2B : c2 ≤ 36 * L + 18 := by
    change c2 ≤ 3 + (36 * L + 14) + 1 at hc2; omega
  have hc3B : c3 ≤ 38 * L + 20 := by
    change c3 ≤ 4 + (38 * L + 15) + 1 at hc3; omega
  have hc4B : c4 ≤ 85 * L + 60 := by
    have harg4 : argsSize [Expr.reg 10, Expr.reg 8, Expr.reg 5, Expr.reg 12] = 4 := rfl
    rw [harg4] at hc4
    dsimp only [Num.subtractContract, heapContract, List.getD] at hc4
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at hc4
    omega
  have rPart1 : Runs w p ω (wireRefreshOnePart1Stmt divide add sub negate) s0 .normal s9
      (c1 + (4 + (c2 + (8 + (c3 + (c4 + (4 + (3 + 5 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, rc1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, c2, _, rc2,
    runs_seq_iff.mpr (Or.inr ⟨s4, 8, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, c3, _, rc3,
    runs_seq_iff.mpr (Or.inr ⟨s6, c4, _, rc4,
    runs_seq_iff.mpr (Or.inr ⟨s7, 4, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 3, 5, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hs9_lt_h4 (a : ℕ) (ha : a < h4) : s9.mem a = s6.mem a := by
    dsimp only [s9, s8, s7]
    rw [Function.update_of_ne (by omega : a ≠ h4 + 1), Function.update_of_ne (by omega : a ≠ h4)]
  refine ⟨s9, c1 + (4 + (c2 + (8 + (c3 + (c4 + (4 + (3 + 5 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1,
    rPart1, by omega,
    (hs9Reg 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s0, startState]),
    (hs9Reg 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s0, startState]),
    (hs9Reg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s0, startState]),
    (hs9Reg 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s0, startState]),
    by simp [s9, s8, s7, hs6Regs 8 (by decide), hs5Regs 8 (by decide), s4, hs3Regs 8 (by decide), s2, hr1_8, h1],
    by rw [← hh4]; simp [s9, s8, s7, hr6_13, h4],
    by rw [← hh3]; simp [s9, s8, s7],
    by rw [← hh4]; dsimp only [s9, s8]; rw [Function.update_of_ne (by omega : h4 ≠ h4 + 1), Function.update_self],
    by rw [← hh4]; dsimp only [s9]; rw [Function.update_self],
    hThrNewAt5.congr (fun j hj => (hs9_lt_h4 _ (by omega)).trans (hFr4 _ (by omega))),
    by rw [← hh3]; exact hDetNewAt6.congr (fun j hj => hs9_lt_h4 _ (by omega)),
    fun a ha => (hs9_lt_h4 a (by omega)).trans ((hFr4 a (by omega)).trans ((hFr3 a (by omega)).trans (hFr30 a ha))),
    fun a ha => by
      dsimp only [s9, s8, s7]
      rw [Function.update_of_ne (by omega : a ≠ h4 + 1), Function.update_of_ne (by omega : a ≠ h4)]
      exact hz4 a (by omega)⟩

/-! ### 2. Second half of `wireRefreshOneAccountBody` (4 copies + `isNeg` + return tuple) -/

private theorem wireRefreshOnePart2_runs
    {w copy isNeg oldRecPtr gPtr lPtr L heap h1 h3 h4 : ℕ}
    {p : Program} {ω : ℕ → Bool} {s9 : State}
    {oldVal : PathEdgeValue} {gNewInt thrNew detNew : ℤ} {lNewInt : ℕ}
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hisNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hLpos : 0 < L)
    (hh1 : h1 = heap + Num.fixedDivideSpace L)
    (hh3 : h3 = h1 + 2 * L) (hh4 : h4 = h1 + 4 * L)
    (hRecLe : oldRecPtr + (2 + 4 * L) ≤ heap) (hGLe : gPtr + L ≤ heap) (hLLe : lPtr + L ≤ heap)
    (hr0 : s9.regs 0 = oldRecPtr) (hr2 : s9.regs 2 = gPtr) (hr3 : s9.regs 3 = lPtr)
    (hr5 : s9.regs 5 = L) (hr8 : s9.regs 8 = h1) (hr13 : s9.regs 13 = h4) (hr14 : s9.regs 14 = h3 + L)
    (hh4_0 : s9.mem h4 = 1) (hh4_1 : s9.mem (h4 + 1) = 1)
    (hOldFlow : PathIntAt s9.mem (oldRecPtr + 2 + 2 * L) 4 L oldVal.flow)
    (hGAt : PathIntAt s9.mem gPtr 4 L gNewInt)
    (hLAt : PathIntAt s9.mem lPtr 4 L (lNewInt : ℤ))
    (hThrAt : PathIntAt s9.mem h1 4 L thrNew)
    (hDetAt : PathIntAt s9.mem (h3 + L) 4 L detNew)
    (hz9 : ∀ a, h4 + 2 ≤ a → s9.mem a = 0)
    (hRoom : heap + wireRefreshOneSpace L < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    let newVal : PathEdgeValue :=
      { forward := true, gradient := gNewInt, length := (lNewInt : ℤ),
        flow := oldVal.flow, detector := detNew }
    let nextHeap := heap + wireRefreshOneSpace L
    ∃ out cB,
      Runs w p ω (wireRefreshOnePart2Stmt copy isNeg) s9 (.returned nextHeap) out cB ∧
      cB ≤ 70 * L + 160 ∧
      out.mem (nextHeap - 3) = h1 ∧
      out.mem (nextHeap - 2) = h4 ∧
      out.mem (nextHeap - 1) = (if detNew < 0 then 1 else 0) ∧
      PathIntAt out.mem h1 4 L thrNew ∧
      PathEdgeAt out.mem h4 4 L (some newVal) ∧
      ZeroFrom out.mem nextHeap ∧
      ∀ a < h4, out.mem a = s9.mem a := by
  dsimp only
  set outRec := h4 + (2 + 4 * L)
  set nextHeap := heap + wireRefreshOneSpace L
  have hNextEq : nextHeap = outRec + 3 := by
    dsimp only [nextHeap, outRec]; unfold wireRefreshOneSpace; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hLW : L < 2 ^ w := by dsimp only [nextHeap] at hRoom; unfold wireRefreshOneSpace at hRoom; omega
  have h4LW : 4 * L < 2 ^ w := by dsimp only [nextHeap] at hRoom; unfold wireRefreshOneSpace at hRoom; omega
  have hRoom' : outRec + 3 < 2 ^ w := by rw [← hNextEq]; exact hRoom
  obtain ⟨s10, c5, _, rc5, hp5, _, hs10Regs, hc5⟩ :=
    runs_call_of_meetsContract (r := 15) (args := [.reg 2, .bin .add (.reg 13) (.const 2), .reg 5])
      hcopy (st := s9) (vs := [gPtr, h4 + 2, L])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hr2, hr5, hr13, hw2, show h4 + 2 < 2 ^ w by omega])
      (by simp [show gPtr < 2 ^ w by omega, show h4 + 2 < 2 ^ w by omega, hLW])
      ⟨gPtr, h4 + 2, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩ ω
  obtain ⟨_, _, _, hArgs5, _, hCopG, hFr5⟩ := hp5
  simp only [List.cons.injEq, and_true] at hArgs5; obtain ⟨rfl, rfl, rfl⟩ := hArgs5
  obtain ⟨s11, c6, _, rc6, hp6, _, hs11Regs, hc6⟩ :=
    runs_call_of_meetsContract (r := 15) (args := [.reg 3, .bin .add (.bin .add (.reg 13) (.const 2)) (.reg 5), .reg 5])
      hcopy (st := s10) (vs := [lPtr, h4 + 2 + L, L])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hs10Regs 3 (by decide), hs10Regs 13 (by decide),
        hs10Regs 5 (by decide), hr3, hr5, hr13, hw2, show h4 + 2 < 2 ^ w by omega,
        show h4 + 2 + L < 2 ^ w by omega])
      (by simp [show lPtr < 2 ^ w by omega, show h4 + 2 + L < 2 ^ w by omega, hLW])
      ⟨lPtr, h4 + 2 + L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩ ω
  obtain ⟨_, _, _, hArgs6, _, hCopL, hFr6⟩ := hp6
  simp only [List.cons.injEq, and_true] at hArgs6; obtain ⟨rfl, rfl, rfl⟩ := hArgs6
  obtain ⟨s12, c7, _, rc7, hp7, _, hs12Regs, hc7⟩ :=
    runs_call_of_meetsContract (r := 15)
      (args := [.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 5)),
        .bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 5)), .reg 5])
      hcopy (st := s11) (vs := [oldRecPtr + 2 + 2 * L, h4 + 2 + 2 * L, L])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hs11Regs 0 (by decide), hs11Regs 13 (by decide),
        hs11Regs 5 (by decide), hs10Regs 0 (by decide), hs10Regs 13 (by decide), hs10Regs 5 (by decide),
        hr0, hr5, hr13, hw2, show 2 * L < 2 ^ w by omega, show oldRecPtr + 2 < 2 ^ w by omega,
        show oldRecPtr + 2 + 2 * L < 2 ^ w by omega, show h4 + 2 < 2 ^ w by omega,
        show h4 + 2 + 2 * L < 2 ^ w by omega])
      (by simp [show oldRecPtr + 2 + 2 * L < 2 ^ w by omega, show h4 + 2 + 2 * L < 2 ^ w by omega, hLW])
      ⟨oldRecPtr + 2 + 2 * L, h4 + 2 + 2 * L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩ ω
  obtain ⟨_, _, _, hArgs7, _, hCopFl, hFr7⟩ := hp7
  simp only [List.cons.injEq, and_true] at hArgs7; obtain ⟨rfl, rfl, rfl⟩ := hArgs7
  obtain ⟨s13, c8, _, rc8, hp8, _, hs13Regs, hc8⟩ :=
    runs_call_of_meetsContract (r := 15)
      (args := [.reg 14, .bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 3) (.reg 5)), .reg 5])
      hcopy (st := s12) (vs := [h3 + L, h4 + 2 + 3 * L, L])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hs12Regs 14 (by decide), hs12Regs 13 (by decide),
        hs12Regs 5 (by decide), hs11Regs 14 (by decide), hs11Regs 13 (by decide), hs11Regs 5 (by decide),
        hs10Regs 14 (by decide), hs10Regs 13 (by decide), hs10Regs 5 (by decide),
        hr14, hr13, hr5, hw2, hw3, show 3 * L < 2 ^ w by omega,
        show h4 + 2 < 2 ^ w by omega, show h4 + 2 + 3 * L < 2 ^ w by omega])
      (by simp [show h3 + L < 2 ^ w by omega, show h4 + 2 + 3 * L < 2 ^ w by omega, hLW])
      ⟨h3 + L, h4 + 2 + 3 * L, L, rfl, hw1, by omega, by omega, Or.inr (by omega)⟩ ω
  obtain ⟨_, _, _, hArgs8, _, hCopDet, hFr8⟩ := hp8
  simp only [List.cons.injEq, and_true] at hArgs8; obtain ⟨rfl, rfl, rfl⟩ := hArgs8
  have h13_lt_h42 (a : ℕ) (ha : a < h4 + 2) : s13.mem a = s9.mem a := by
    rw [hFr8 a (Or.inl (by omega)), hFr7 a (Or.inl (by omega)), hFr6 a (Or.inl (by omega)),
      hFr5 a (Or.inl (by omega))]
  have hDetAt13 : PathIntAt s13.mem (h3 + L) 4 L detNew :=
    hDetAt.congr (fun j hj => h13_lt_h42 _ (by omega))
  obtain ⟨s14, c9, negBit, rc9, hp9, hr14_16, hs14Regs, hc9⟩ :=
    runs_call_of_meetsContract (r := 16) (args := [.reg 14, .reg 5])
      hisNeg (st := s13) (vs := [h3 + L, L])
      (by simp [evalArgs, Expr.eval, hs13Regs 14 (by decide), hs13Regs 5 (by decide),
        hs12Regs 14 (by decide), hs12Regs 5 (by decide), hs11Regs 14 (by decide), hs11Regs 5 (by decide),
        hs10Regs 14 (by decide), hs10Regs 5 (by decide), hr14, hr5])
      (by simp [show h3 + L < 2 ^ w by omega, hLW])
      ⟨h3 + L, L, rfl, by omega, hDetAt13.1⟩ ω
  obtain ⟨hs14Mem, hNegBitEq⟩ := hp9
  have hNegBitVal : negBit = if detNew < 0 then 1 else 0 := by
    simpa [hDetAt13.2] using hNegBitEq
  have hs14_r (r : ℕ) (h15 : r ≠ 15) (h16 : r ≠ 16) : s14.regs r = s9.regs r := by
    rw [hs14Regs r h16, hs13Regs r h15, hs12Regs r h15, hs11Regs r h15, hs10Regs r h15]
  let s15 := { s14 with regs := Function.update s14.regs 17 outRec }
  let s16 := { s15 with mem := Function.update s15.mem outRec h1 }
  let s17 := { s16 with mem := Function.update s16.mem (outRec + 1) h4 }
  let s18 := { s17 with mem := Function.update s17.mem (outRec + 2) negBit }
  have r15 : Runs w p ω (.assign 17 (.bin .add (.reg 13) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 5)))))
      s14 .normal s15 8 :=
    runs_assign_iff.mpr ⟨outRec, by
      simp [Expr.eval, BinOp.eval, hs14_r 13 (by decide) (by decide), hs14_r 5 (by decide) (by decide),
        hr13, hr5, hw2, hw4, h4LW, show 2 + 4 * L < 2 ^ w by omega, show outRec < 2 ^ w by omega, outRec],
      rfl, rfl, rfl⟩
  have r16 : Runs w p ω (.store (.reg 17) (.reg 8)) s15 .normal s16 3 :=
    runs_store_iff.mpr ⟨outRec, h1, by simp [Expr.eval, s15],
      by simp [Expr.eval, s15, hs14_r 8 (by decide) (by decide), hr8], rfl, rfl, rfl⟩
  have r17 : Runs w p ω (.store (.bin .add (.reg 17) (.const 1)) (.reg 13)) s16 .normal s17 5 :=
    runs_store_iff.mpr ⟨outRec + 1, h4, by
      simp [Expr.eval, BinOp.eval, s16, s15, hw1, show outRec + 1 < 2 ^ w by omega],
      by simp [Expr.eval, s16, s15, hs14_r 13 (by decide) (by decide), hr13], rfl, rfl, rfl⟩
  have r18 : Runs w p ω (.store (.bin .add (.reg 17) (.const 2)) (.reg 16)) s17 .normal s18 5 :=
    runs_store_iff.mpr ⟨outRec + 2, negBit, by
      simp [Expr.eval, BinOp.eval, s17, s16, s15, hw2, show outRec + 2 < 2 ^ w by omega],
      by simp [Expr.eval, s17, s16, s15, hr14_16], rfl, rfl, rfl⟩
  have r19 : Runs w p ω (.ret (.bin .add (.reg 17) (.const 3))) s18 (.returned nextHeap) s18 4 :=
    runs_ret_iff.mpr ⟨nextHeap, by
      simp [Expr.eval, BinOp.eval, s18, s17, s16, s15, hw3, hNextEq, show outRec + 3 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have rPart2 : Runs w p ω (wireRefreshOnePart2Stmt copy isNeg) s9 (.returned nextHeap) s18
      (c5 + (c6 + (c7 + (c8 + (c9 + (8 + (3 + (5 + (5 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s10, c5, _, rc5,
    runs_seq_iff.mpr (Or.inr ⟨s11, c6, _, rc6,
    runs_seq_iff.mpr (Or.inr ⟨s12, c7, _, rc7,
    runs_seq_iff.mpr (Or.inr ⟨s13, c8, _, rc8,
    runs_seq_iff.mpr (Or.inr ⟨s14, c9, _, rc9,
    runs_seq_iff.mpr (Or.inr ⟨s15, 8, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 3, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s17, 5, _, r17,
    runs_seq_iff.mpr (Or.inr ⟨s18, 5, 4, r18, r19, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hc5B : c5 ≤ 17 * L + 16 := by change c5 ≤ 5 + (17 * L + 10) + 1 at hc5; omega
  have hc6B : c6 ≤ 17 * L + 18 := by change c6 ≤ 7 + (17 * L + 10) + 1 at hc6; omega
  have hc7B : c7 ≤ 17 * L + 26 := by change c7 ≤ 15 + (17 * L + 10) + 1 at hc7; omega
  have hc8B : c8 ≤ 17 * L + 20 := by change c8 ≤ 9 + (17 * L + 10) + 1 at hc8; omega
  have hc9B : c9 ≤ 16 := by change c9 ≤ 2 + 13 + 1 at hc9; omega
  have h18_lt_out (a : ℕ) (ha : a < outRec) : s18.mem a = s13.mem a := by
    dsimp only [s18, s17, s16, s15]
    rw [Function.update_of_ne (by omega : a ≠ outRec + 2),
      Function.update_of_ne (by omega : a ≠ outRec + 1),
      Function.update_of_ne (by omega : a ≠ outRec), hs14Mem]
  have h18_o0 : s18.mem outRec = h1 := by
    dsimp only [s18, s17, s16]
    rw [Function.update_of_ne (by omega : outRec ≠ outRec + 2),
      Function.update_of_ne (by omega : outRec ≠ outRec + 1), Function.update_self]
  have h18_o1 : s18.mem (outRec + 1) = h4 := by
    dsimp only [s18, s17]
    rw [Function.update_of_ne (by omega : outRec + 1 ≠ outRec + 2), Function.update_self]
  have h18_o2 : s18.mem (outRec + 2) = negBit := by
    dsimp only [s18]; rw [Function.update_self]
  refine ⟨s18,
    c5 + (c6 + (c7 + (c8 + (c9 + (8 + (3 + (5 + (5 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1,
    rPart2, by omega,
    by rw [show nextHeap - 3 = outRec by omega]; exact h18_o0,
    by rw [show nextHeap - 2 = outRec + 1 by omega]; exact h18_o1,
    by rw [show nextHeap - 1 = outRec + 2 by omega, h18_o2]; exact hNegBitVal,
    hThrAt.congr (fun j hj => (h18_lt_out _ (by omega)).trans (h13_lt_h42 _ (by omega))),
    ⟨(h18_lt_out h4 (by omega)).trans ((h13_lt_h42 h4 (by omega)).trans hh4_0),
     (h18_lt_out (h4 + 1) (by omega)).trans ((h13_lt_h42 (h4 + 1) (by omega)).trans hh4_1),
     hGAt.congr (fun j hj => by
       rw [h18_lt_out _ (by omega), hFr8 _ (Or.inl (by omega)), hFr7 _ (Or.inl (by omega)),
         hFr6 _ (Or.inl (by omega)), hCopG j hj]),
     hLAt.congr (fun j hj => by
       rw [h18_lt_out _ (by omega), hFr8 _ (Or.inl (by omega)), hFr7 _ (Or.inl (by omega)),
         hCopL j hj, hFr5 _ (Or.inl (by omega))]),
     hOldFlow.congr (fun j hj => by
       rw [h18_lt_out _ (by omega), hFr8 _ (Or.inl (by omega)), hCopFl j hj,
         hFr6 _ (Or.inl (by omega)), hFr5 _ (Or.inl (by omega))]),
     hDetAt.congr (fun j hj => by
       rw [h18_lt_out _ (by omega), hCopDet j hj, hFr7 _ (Or.inl (by omega)),
         hFr6 _ (Or.inl (by omega)), hFr5 _ (Or.inl (by omega))])⟩,
    fun a ha => by
      have h18_13 : s18.mem a = s13.mem a := by
        dsimp only [s18, s17, s16, s15]
        rw [Function.update_of_ne (by omega : a ≠ outRec + 2),
          Function.update_of_ne (by omega : a ≠ outRec + 1),
          Function.update_of_ne (by omega : a ≠ outRec), hs14Mem]
      rw [h18_13, hFr8 a (Or.inr (by omega)), hFr7 a (Or.inr (by omega)),
        hFr6 a (Or.inr (by omega)), hFr5 a (Or.inr (by omega))]
      exact hz9 a (by omega),
    fun a ha => (h18_lt_out a (by omega)).trans (h13_lt_h42 a (by omega))⟩

/-! ### 3. Full execution of `wireRefreshOneAccountBody` -/

private theorem runs_seq_assoc {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b c : Stmt}
    {s out : State} {o : Outcome} {cost : ℕ}
    (h : Runs w p ω ((a ;; b) ;; c) s o out cost) :
    ∃ cost', Runs w p ω (a ;; (b ;; c)) s o out cost' ∧ cost' ≤ cost := by
  rcases runs_seq_iff.mp h with ⟨v, c1, hAB, rfl, rfl⟩ | ⟨s2, cab, cc, hAB, hC, rfl⟩
  · rcases runs_seq_iff.mp hAB with ⟨v', c0, hA, hEq, rfl⟩ | ⟨s1, ca, cb, hA, hB, rfl⟩
    · cases hEq
      exact ⟨c0 + 1, runs_seq_iff.mpr (Or.inl ⟨v, c0, hA, rfl, rfl⟩), by omega⟩
    · exact ⟨ca + (cb + 1) + 1,
        runs_seq_iff.mpr (Or.inr ⟨s1, ca, cb + 1, hA,
          runs_seq_iff.mpr (Or.inl ⟨v, cb, hB, rfl, rfl⟩), rfl⟩), by omega⟩
  · rcases runs_seq_iff.mp hAB with ⟨_, _, _, hEq, _⟩ | ⟨s1, ca, cb, hA, hB, rfl⟩
    · cases hEq
    · exact ⟨ca + (cb + cc + 1) + 1,
        runs_seq_iff.mpr (Or.inr ⟨s1, ca, cb + cc + 1, hA,
          runs_seq_iff.mpr (Or.inr ⟨s2, cb, cc, hB, hC, rfl⟩), rfl⟩), by omega⟩

private theorem runs_seq_lift {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b b' : Stmt}
    {s out : State} {o : Outcome} {cost : ℕ}
    (f : ∀ {s' out' o' c'}, Runs w p ω b s' o' out' c' → ∃ c'', Runs w p ω b' s' o' out' c'' ∧ c'' ≤ c')
    (hr : Runs w p ω (a ;; b) s o out cost) :
    ∃ cost', Runs w p ω (a ;; b') s o out cost' ∧ cost' ≤ cost := by
  rcases runs_seq_iff.mp hr with ⟨v, c1, hA, rfl, rfl⟩ | ⟨sm, ca, cb, hA, hB, rfl⟩
  · exact ⟨c1 + 1, runs_seq_iff.mpr (Or.inl ⟨v, c1, hA, rfl, rfl⟩), le_rfl⟩
  · obtain ⟨cb', hB', hle⟩ := f hB
    exact ⟨ca + cb' + 1, runs_seq_iff.mpr (Or.inr ⟨sm, ca, cb', hA, hB', rfl⟩), by omega⟩

private theorem runs_seq_right_of_part1 {w divide add sub negate : ℕ} {tail : Stmt}
    {p : Program} {ω : ℕ → Bool} {s out : State} {o : Outcome} {cost : ℕ}
    (h : Runs w p ω (wireRefreshOnePart1Stmt divide add sub negate ;; tail) s o out cost) :
    ∃ cost', Runs w p ω
      (.call 8 divide [.reg 4, .reg 3, .reg 5, .reg 6, .reg 7] ;;
       .assign 9 (.bin .sub (.reg 8) (.reg 5)) ;;
       .call 10 negate [.reg 9, .reg 5, .reg 8] ;;
       .assign 11 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 3) (.reg 5))) ;;
       .call 12 add [.reg 11, .reg 1, .reg 5, .reg 10] ;;
       .call 13 sub [.reg 10, .reg 8, .reg 5, .reg 12] ;;
       .assign 14 (.bin .add (.reg 12) (.reg 5)) ;;
       .store (.reg 13) (.const 1) ;;
       .store (.bin .add (.reg 13) (.const 1)) (.const 1) ;; tail) s o out cost' ∧ cost' ≤ cost := by
  unfold wireRefreshOnePart1Stmt at h
  obtain ⟨c1, h1, hle1⟩ := runs_seq_assoc h
  have step {a b b' : Stmt} {s0 s1 : State} {o0 : Outcome} {c0 : ℕ}
      (hr : Runs w p ω (a ;; b) s0 o0 s1 c0)
      (f : ∀ {s' out' o' c'}, Runs w p ω b s' o' out' c' → ∃ c'', Runs w p ω b' s' o' out' c'' ∧ c'' ≤ c') :=
    runs_seq_lift f hr
  have comp {x y z : Stmt}
      (f : ∀ {s' out' o' c'}, Runs w p ω x s' o' out' c' → ∃ c'', Runs w p ω y s' o' out' c'' ∧ c'' ≤ c')
      (g : ∀ {s' out' o' c'}, Runs w p ω y s' o' out' c' → ∃ c'', Runs w p ω z s' o' out' c'' ∧ c'' ≤ c') :
      ∀ {s' out' o' c'}, Runs w p ω x s' o' out' c' → ∃ c'', Runs w p ω z s' o' out' c'' ∧ c'' ≤ c' :=
    fun hx => by obtain ⟨cy, hy, h1⟩ := f hx; obtain ⟨cz, hz, h2⟩ := g hy; exact ⟨cz, hz, h2.trans h1⟩
  obtain ⟨c2, h2, hle2⟩ := step h1 (comp runs_seq_assoc (runs_seq_lift (comp runs_seq_assoc
    (runs_seq_lift (comp runs_seq_assoc (runs_seq_lift (comp runs_seq_assoc
    (runs_seq_lift (comp runs_seq_assoc (runs_seq_lift (comp runs_seq_assoc
    (runs_seq_lift runs_seq_assoc))))))))))))
  exact ⟨c2, h2, hle2.trans hle1⟩

/-- Execute `wireRefreshOneAccountBody` to compute `(thrNewPtr, recNewPtr, isNegBit)` for one
replaced edge, preserving its exact `flow` and `detectAccum` while updating `(gradient, length,
detectorThreshold)`. -/
theorem wireRefreshOneAccountBody_runs
    {w divide add sub negate copy isNeg oldRecPtr oldThrPtr gPtr lPtr negEpsPtr L P heap pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {oldVal : PathEdgeValue} {epsInt gNewInt oldThr acc : ℤ} {lNewInt : ℕ}
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hadd : MeetsContract w p add (Num.addContract w 4))
    (hsub : MeetsContract w p sub (Num.subtractContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hisNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hLpos : 0 < L) (hlPos : 0 < lNewInt)
    (hRecLe : oldRecPtr + (2 + 4 * L) ≤ heap) (hThrLe : oldThrPtr + L ≤ heap)
    (hGLe : gPtr + L ≤ heap) (hLLe : lPtr + L ≤ heap) (hEpsLe : negEpsPtr + L ≤ heap)
    (hOldRec : PathEdgeAt mem oldRecPtr 4 L (some oldVal))
    (_hOldFwd : oldVal.forward = true)
    (hOldThr : PathIntAt mem oldThrPtr 4 L oldThr)
    (hOldDet : oldVal.detector = acc - oldThr)
    (hNegEps : PathIntAt mem negEpsPtr 4 L (-epsInt))
    (hGAt : PathIntAt mem gPtr 4 L gNewInt)
    (hLAt : PathIntAt mem lPtr 4 L (lNewInt : ℤ))
    (_hEpsPos : (0 : ℝ) < (epsInt : ℝ) / (2 : ℝ) ^ P)
    (hFitNegThr : Num.Fits 4 L (-detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lNewInt : ℝ) / (2 : ℝ) ^ P)))
    (hFitPosThr : Num.Fits 4 L (detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lNewInt : ℝ) / (2 : ℝ) ^ P)))
    (hFitAcc : Num.Fits 4 L acc)
    (hFitDetNew : Num.Fits 4 L (acc - detectorThreshold P ((epsInt : ℝ) / (2 : ℝ) ^ P)
      ((lNewInt : ℝ) / (2 : ℝ) ^ P)))
    (hz : ZeroFrom mem heap)
    (hRoom : heap + wireRefreshOneSpace L < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    let ε := (epsInt : ℝ) / (2 : ℝ) ^ P
    let thrNew := detectorThreshold P ε ((lNewInt : ℝ) / (2 : ℝ) ^ P)
    let newVal : PathEdgeValue :=
      { forward := true, gradient := gNewInt, length := (lNewInt : ℤ),
        flow := oldVal.flow, detector := acc - thrNew }
    let nextHeap := heap + wireRefreshOneSpace L
    let thrNewPtr := heap + Num.fixedDivideSpace L
    let recNewPtr := thrNewPtr + 4 * L
    ∃ out cost,
      Runs w p ω (wireRefreshOneAccountBody divide add sub negate copy isNeg)
        (startState [oldRecPtr, oldThrPtr, gPtr, lPtr, negEpsPtr, L, P, heap] mem pos)
        (.returned nextHeap) out cost ∧
      cost ≤ wireRefreshOneCost L ∧
      out.mem (nextHeap - 3) = thrNewPtr ∧
      out.mem (nextHeap - 2) = recNewPtr ∧
      out.mem (nextHeap - 1) = (if acc - thrNew < 0 then 1 else 0) ∧
      PathIntAt out.mem thrNewPtr 4 L thrNew ∧
      PathEdgeAt out.mem recNewPtr 4 L (some newVal) ∧
      ZeroFrom out.mem nextHeap ∧
      ∀ a < heap, out.mem a = mem a := by
  dsimp only
  obtain ⟨s9, cA, rA, hcA, hr0, hr2, hr3, hr5, hr8, hr13, hr14, hh4_0, hh4_1, hThr9, hDet9, hFr9, hz9⟩ :=
    wireRefreshOnePart1_runs (w := w) (p := p) (ω := ω) (pos := pos)
      hdiv hadd hsub hneg hPdiv hPword hLpos hlPos hRecLe hThrLe hLLe hEpsLe
      hOldRec hOldThr hOldDet hNegEps hLAt hFitNegThr hFitPosThr hFitAcc hFitDetNew hz hRoom hw4
  obtain ⟨out, cB, rB, hcB, ho0, ho1, ho2, hThrOut, hRecOut, hzOut, hFrOut⟩ :=
    wireRefreshOnePart2_runs (w := w) (p := p) (ω := ω) (s9 := s9) (oldVal := oldVal)
      (gNewInt := gNewInt) (lNewInt := lNewInt) hcopy hisNeg hLpos rfl rfl rfl
      hRecLe hGLe hLLe hr0 hr2 hr3 hr5 hr8 hr13 hr14 hh4_0 hh4_1
      (hOldRec.2.2.2.2.1.congr (fun j hj => hFr9 _ (by omega)))
      (hGAt.congr (fun j hj => hFr9 _ (by omega)))
      (hLAt.congr (fun j hj => hFr9 _ (by omega)))
      hThr9 hDet9 hz9 hRoom hw4
  have rSeq : Runs w p ω (wireRefreshOnePart1Stmt divide add sub negate ;; wireRefreshOnePart2Stmt copy isNeg)
      (startState [oldRecPtr, oldThrPtr, gPtr, lPtr, negEpsPtr, L, P, heap] mem pos)
      (.returned (heap + wireRefreshOneSpace L)) out (cA + cB + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s9, cA, cB, rA, rB, rfl⟩)
  obtain ⟨cAll, rBody, hcAllLe⟩ := runs_seq_right_of_part1 rSeq
  exact ⟨out, cAll, rBody, by dsimp [wireRefreshOneCost]; omega, ho0, ho1, ho2,
    hThrOut, hRecOut, hzOut, fun a ha => (hFrOut a (by omega)).trans (hFr9 a ha)⟩

end MinCostFlow.MinRatio
