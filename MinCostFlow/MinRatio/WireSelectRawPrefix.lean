module

public import MinCostFlow.MinRatio.WireSelectRawCoreTok
public import MinCostFlow.MinRatio.ShiftLoopLevelFacts
import WordRAM.Tactic

/-!
# Common prefix execution for `selectRawRouteBody`

Extracts the 20-step nonempty-heap prefix of `selectRawRouteBody` (`WireSelectQuery.lean`) into a
standalone lemma `selectRawRoute_prefix_runs` so that `WireSelectRawProofs.lean` stays compact and
below the 800-line ceiling.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

/-- Executes the nonempty-heap prefix of `selectRawRouteBody` (header reads, `isNeg`, `isZero`,
orientation bit `flip`, and root-graph pointer computation) up to `.cond (.bin .eq (.reg 10) (.reg 16))`. -/
theorem selectRawRoute_prefix_runs
    {w isNegProc isZeroProc fillRev splitSteps emitStitches
      root hb descBase workHeap size Lk arrPtr lvlPtr numBase eBest i
      handle d slots rootGraph vCap0 eCap0 : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {flip : Bool}
    (hw16 : 16 < 2 ^ w)
    (hIsNeg : MeetsContract w p isNegProc (Num.isNegativeContract w 4))
    (hIsZero : MeetsContract w p isZeroProc (Num.isZeroContract w 4))
    (hszNZ : size ≠ 0)
    (hhdSize : mem hb = size)
    (hLkHdr : mem (hb + shLkOff) = Lk)
    (hArrHdr : mem (hb + shArrOff) = arrPtr)
    (hLvlHdr : mem (hb + shLvlOff) = lvlPtr)
    (hNumHdr : mem (hb + shNumOff) = numBase)
    (heBestRd : mem arrPtr = eBest)
    (hiRd : mem (lvlPtr + eBest) = i)
    (hNumValid : Num.Valid mem (numBase + eBest * Lk) 4 Lk)
    (hFlipBit :
      (if ((if Num.intVal mem (numBase + eBest * Lk) 4 Lk < 0 then 1 else 0) +
           (if Num.intVal mem (numBase + eBest * Lk) 4 Lk = 0 then 1 else 0)) = 0 then 1 else 0) =
      (if flip then 1 else 0))
    (hHandle : mem root = handle)
    (hD11 : mem (handle + 11) = d)
    (hSlots : mem (root + 6) = slots)
    (hRootG : mem (root + 14) = rootGraph)
    (hRootVC : mem rootGraph = vCap0)
    (hRootEC : mem (rootGraph + 1) = eCap0)
    (hBds : hb + shNumOff < 2 ^ w ∧ lvlPtr + eBest < 2 ^ w ∧
      numBase + eBest * Lk + Lk < 2 ^ w ∧
      root + 14 < 2 ^ w ∧ handle + 11 < 2 ^ w ∧
      rootGraph + dynGraphSize vCap0 eCap0 < 2 ^ w ∧
      Lk < 2 ^ w) :
    ∃ (regsP : ℕ → ℕ) (posP kP : ℕ),
      (∀ (Q : Outcome → State → Prop) (T : ℕ),
        (∃ o st' c, Runs w p ω
          (.cond (.bin .eq (.reg 10) (.reg 16))
            (.assign 24 (.reg 3) ;;
             .assign 25 (.bin .add (.reg 3) (.const 2)) ;;
             .assign 26 (.bin .sub (.const 1) (.reg 14)) ;;
             .assign 27 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 22) (.reg 9))))) ;;
             .assign 28 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 23) (.reg 9))))) ;;
             .store (.reg 24) (.reg 9) ;;
             .store (.bin .add (.reg 24) (.const 1)) (.reg 26) ;;
             .cond (.reg 26)
               (.store (.reg 25) (.reg 28) ;; .store (.bin .add (.reg 25) (.const 1)) (.reg 27))
               (.store (.reg 25) (.reg 27) ;; .store (.bin .add (.reg 25) (.const 1)) (.reg 28)) ;;
             .store (.bin .add (.reg 2) (.const 2)) (.reg 24) ;;
             .store (.bin .add (.reg 2) (.const 3)) (.const 1) ;;
             .store (.bin .add (.reg 2) (.const 4)) (.reg 25) ;;
             .store (.bin .add (.reg 2) (.const 5)) (.const 1) ;;
             .ret (.bin .add (.reg 3) (.const 4)))
            (.assign 27 (.load (.bin .add (.reg 1) (.const shMetaOff))) ;;
             .assign 28 (.bin .add (.bin .add (.reg 27) (.const smTableOff))
               (.bin .add (.bin .mul (.const 5) (.bin .add (.reg 16) (.const 1))) (.reg 10))) ;;
             .assign 30 (.load (.reg 28)) ;;
             .assign 31 (.load (.bin .add (.reg 30) (.reg 9))) ;;
             .assign 32 (.load (.reg 31)) ;;
             .assign 33 (.bin .add (.reg 32) (.const 1)) ;;
             .assign 34 (.reg 3) ;;
             .assign 35 (.bin .add (.reg 34) (.bin .mul (.const 2) (.reg 33))) ;;
             .assign 36 (.bin .add (.reg 35) (.bin .mul (.const 2) (.reg 33))) ;;
             .assign 37 (.bin .add (.reg 36) (.bin .mul (.const 4) (.reg 33))) ;;
             .store (.reg 34) (.reg 9) ;;
             .store (.bin .add (.reg 34) (.const 1)) (.const 1) ;;
             .call 38 fillRev [.reg 31, .reg 32, .reg 34, .const 0] ;;
             .store (.bin .add (.reg 2) (.const 2)) (.reg 35) ;;
             .store (.bin .add (.reg 2) (.const 3)) (.const 0) ;;
             .store (.bin .add (.reg 2) (.const 4)) (.reg 36) ;;
             .store (.bin .add (.reg 2) (.const 5)) (.const 0) ;;
             .call 38 splitSteps [.reg 17, .reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
               .reg 35, .reg 36, .reg 2, .const 0] ;;
             .call 38 emitStitches [.reg 21, .reg 22, .reg 23, .reg 34, .reg 33, .reg 14,
               .reg 36, .reg 2, .const 0] ;;
             .ret (.reg 37)))
          ⟨mem, regsP, posP⟩ o st' c ∧ Q o st' ∧ kP + c ≤ T) →
        ∃ o st' c, Runs w p ω
          (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches)
          (startState [root, hb, descBase, workHeap] mem pos) o st' c ∧ Q o st' ∧ c ≤ T) ∧
      regsP 0 = root ∧ regsP 1 = hb ∧ regsP 2 = descBase ∧ regsP 3 = workHeap ∧
      regsP 9 = eBest ∧ regsP 10 = i ∧ regsP 14 = (if flip then 1 else 0) ∧
      regsP 15 = handle ∧ regsP 16 = d ∧ regsP 17 = slots ∧
      regsP 20 = eCap0 ∧
      regsP 21 = dgIntToExtBase rootGraph vCap0 ∧
      regsP 22 = dgETailSlotBase rootGraph vCap0 eCap0 ∧
      regsP 23 = dgEHeadSlotBase rootGraph vCap0 eCap0 ∧
      kP ≤ 19 * Lk + 160 := by
  have hdgsz : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  obtain ⟨hbW, hlvlW, hnumW, hrtW, hhdlW, hrgW, hLkW⟩ := hBds
  set isNegVal : ℕ := if Num.intVal mem (numBase + eBest * Lk) 4 Lk < 0 then 1 else 0
  set isZeroVal : ℕ := if Num.intVal mem (numBase + eBest * Lk) 4 Lk = 0 then 1 else 0
  obtain ⟨bNeg, hbNeg, oNeg, stNeg, cNeg, hrNeg, hNegPost, hcNeg⟩ :=
    hIsNeg [numBase + eBest * Lk, Lk] mem pos ω
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> omega)
      ⟨numBase + eBest * Lk, Lk, rfl, hnumW, hNumValid⟩
  obtain ⟨hmNeg, hvNeg⟩ := hNegPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hvNeg
  obtain ⟨bZero, hbZero, oZero, stZero, cZero, hrZero, hZeroPost, hcZero⟩ :=
    hIsZero [numBase + eBest * Lk, Lk] mem stNeg.pos ω
      (by intro v hv; simp at hv; rcases hv with rfl | rfl <;> omega)
      ⟨numBase + eBest * Lk, Lk, rfl, hnumW, hNumValid⟩
  obtain ⟨hmZero, hvZero⟩ := hZeroPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hvZero
  have hcNegLe : cNeg ≤ 13 := hcNeg
  have hcZeroLe : cZero ≤ 19 * Lk + 6 := by simpa [Num.isZeroContract] using hcZero
  let s0 := startState [root, hb, descBase, workHeap] mem pos
  let rg4 := Function.update s0.regs 4 size
  let rg5 := Function.update rg4 5 Lk
  let rg6 := Function.update rg5 6 arrPtr
  let rg7 := Function.update rg6 7 lvlPtr
  let rg8 := Function.update rg7 8 numBase
  let rg9 := Function.update rg8 9 eBest
  let rg10 := Function.update rg9 10 i
  let rg11 := Function.update rg10 11 (numBase + eBest * Lk)
  let rg12 := Function.update rg11 12 isNegVal
  let rg13 := Function.update rg12 13 isZeroVal
  let rg14 := Function.update rg13 14 (if flip then 1 else 0)
  let rg15 := Function.update rg14 15 handle
  let rg16 := Function.update rg15 16 d
  let rg17 := Function.update rg16 17 slots
  let rg18 := Function.update rg17 18 rootGraph
  let rg19 := Function.update rg18 19 vCap0
  let rg20 := Function.update rg19 20 eCap0
  let rg21 := Function.update rg20 21 (dgIntToExtBase rootGraph vCap0)
  let rg22 := Function.update rg21 22 (dgETailSlotBase rootGraph vCap0 eCap0)
  let rg23 := Function.update rg22 23 (dgEHeadSlotBase rootGraph vCap0 eCap0)
  refine ⟨rg23, stZero.pos, cNeg + cZero + 135, ?_,
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15, rg14, rg13, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, s0, startState],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15, rg14, rg13, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, s0, startState],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15, rg14, rg13, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, s0, startState],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15, rg14, rg13, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, s0, startState],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15, rg14, rg13, rg12, rg11, rg10, rg9],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15, rg14, rg13, rg12, rg11, rg10],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15, rg14],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16, rg15],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17, rg16],
    by simp [rg23, rg22, rg21, rg20, rg19, rg18, rg17],
    by simp [rg23, rg22, rg21, rg20],
    by simp [rg23, rg22, rg21],
    by simp [rg23, rg22],
    by simp [rg23],
    by omega⟩
  intro Q T ⟨o, st', c, hrRest, hQ, hcT⟩
  have hNegZeroW : isNegVal + isZeroVal < 2 ^ w := by dsimp only [isNegVal, isZeroVal]; split <;> split <;> omega
  have hflBitW : (if flip then 1 else 0) < 2 ^ w := by split <;> omega
  simp only [shLkOff, shArrOff, shLvlOff, shNumOff] at hbW hLkHdr hArrHdr hLvlHdr hNumHdr
  have hStep4 : Runs w p ω (.assign 4 (.load (.reg 1))) s0 .normal ⟨mem, rg4, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨size, by simp [Expr.eval, s0, startState, hhdSize], rfl, rfl, rfl⟩
  have hStep5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 1) (.const shLkOff))))
      ⟨mem, rg4, pos⟩ .normal ⟨mem, rg5, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨Lk, by simp [Expr.eval, BinOp.eval, rg4, s0, startState, shLkOff,
      show 3 < 2 ^ w by omega, show hb + 3 < 2 ^ w by omega, hLkHdr], rfl, rfl, rfl⟩
  have hStep6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 1) (.const shArrOff))))
      ⟨mem, rg5, pos⟩ .normal ⟨mem, rg6, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨arrPtr, by simp [Expr.eval, BinOp.eval, rg5, rg4, s0, startState, shArrOff,
      show 4 < 2 ^ w by omega, show hb + 4 < 2 ^ w by omega, hArrHdr], rfl, rfl, rfl⟩
  have hStep7 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 1) (.const shLvlOff))))
      ⟨mem, rg6, pos⟩ .normal ⟨mem, rg7, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨lvlPtr, by simp [Expr.eval, BinOp.eval, rg6, rg5, rg4, s0, startState, shLvlOff,
      show 6 < 2 ^ w by omega, show hb + 6 < 2 ^ w by omega, hLvlHdr], rfl, rfl, rfl⟩
  have hStep8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 1) (.const shNumOff))))
      ⟨mem, rg7, pos⟩ .normal ⟨mem, rg8, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨numBase, by simp [Expr.eval, BinOp.eval, rg7, rg6, rg5, rg4, s0, startState, shNumOff,
      show 7 < 2 ^ w by omega, show hb + 7 < 2 ^ w by omega, hNumHdr], rfl, rfl, rfl⟩
  have hStep9 : Runs w p ω (.assign 9 (.load (.reg 6)))
      ⟨mem, rg8, pos⟩ .normal ⟨mem, rg9, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨eBest, by simp [Expr.eval, rg8, rg7, rg6, heBestRd], rfl, rfl, rfl⟩
  have hStep10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 7) (.reg 9))))
      ⟨mem, rg9, pos⟩ .normal ⟨mem, rg10, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨i, by simp [Expr.eval, BinOp.eval, rg9, rg8, rg7, hlvlW, hiRd], rfl, rfl, rfl⟩
  have hStep11 : Runs w p ω (.assign 11 (.bin .add (.reg 8) (.bin .mul (.reg 9) (.reg 5))))
      ⟨mem, rg10, pos⟩ .normal ⟨mem, rg11, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨numBase + eBest * Lk,
      by simp [Expr.eval, BinOp.eval, rg10, rg9, rg8, rg7, rg6, rg5,
        show eBest * Lk < 2 ^ w by omega, show numBase + eBest * Lk < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hStep12 : Runs w p ω (.call 12 isNegProc [.reg 11, .reg 5])
      ⟨mem, rg11, pos⟩ .normal ⟨mem, rg12, stNeg.pos⟩ (cNeg + 3) :=
    runs_call_iff.mpr ⟨[numBase + eBest * Lk, Lk], bNeg, oNeg, stNeg, cNeg,
      by simp [evalArgs, Expr.eval, rg11, rg10, rg9, rg8, rg7, rg6, rg5], hbNeg, hrNeg,
      rfl, by simp [rg12, hmNeg, hvNeg, isNegVal], by simp [argsSize, Expr.size]; omega⟩
  have hStep13 : Runs w p ω (.call 13 isZeroProc [.reg 11, .reg 5])
      ⟨mem, rg12, stNeg.pos⟩ .normal ⟨mem, rg13, stZero.pos⟩ (cZero + 3) :=
    runs_call_iff.mpr ⟨[numBase + eBest * Lk, Lk], bZero, oZero, stZero, cZero,
      by simp [evalArgs, Expr.eval, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5], hbZero, hrZero,
      rfl, by simp [rg13, hmZero, hvZero, isZeroVal], by simp [argsSize, Expr.size]; omega⟩
  have hStep14 : Runs w p ω (.assign 14 (.bin .eq (.bin .add (.reg 12) (.reg 13)) (.const 0)))
      ⟨mem, rg13, stZero.pos⟩ .normal ⟨mem, rg14, stZero.pos⟩ 6 :=
    runs_assign_iff.mpr ⟨if flip then 1 else 0, by
      simp [Expr.eval, BinOp.eval, rg13, rg12, show 0 < 2 ^ w by omega, hNegZeroW]
      exact ⟨by split <;> omega, by simpa [Nat.add_eq_zero_iff] using hFlipBit⟩,
      rfl, rfl, rfl⟩
  have hStep15 : Runs w p ω (.assign 15 (.load (.reg 0)))
      ⟨mem, rg14, stZero.pos⟩ .normal ⟨mem, rg15, stZero.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨handle,
      by simp [Expr.eval, rg14, rg13, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, s0, startState, hHandle],
      rfl, rfl, rfl⟩
  have hStep16 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 15) (.const 11))))
      ⟨mem, rg15, stZero.pos⟩ .normal ⟨mem, rg16, stZero.pos⟩ 5 :=
    runs_assign_iff.mpr ⟨d,
      by simp [Expr.eval, BinOp.eval, rg15, show 11 < 2 ^ w by omega, hhdlW, hD11], rfl, rfl, rfl⟩
  have hStep17 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 0) (.const 6))))
      ⟨mem, rg16, stZero.pos⟩ .normal ⟨mem, rg17, stZero.pos⟩ 5 :=
    runs_assign_iff.mpr ⟨slots,
      by simp [Expr.eval, BinOp.eval, rg16, rg15, rg14, rg13, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, s0, startState,
        show 6 < 2 ^ w by omega, show root + 6 < 2 ^ w by omega, hSlots], rfl, rfl, rfl⟩
  have hStep18 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 0) (.const 14))))
      ⟨mem, rg17, stZero.pos⟩ .normal ⟨mem, rg18, stZero.pos⟩ 5 :=
    runs_assign_iff.mpr ⟨rootGraph,
      by simp [Expr.eval, BinOp.eval, rg17, rg16, rg15, rg14, rg13, rg12, rg11, rg10, rg9, rg8, rg7, rg6, rg5, rg4, s0, startState,
        show 14 < 2 ^ w by omega, hrtW, hRootG], rfl, rfl, rfl⟩
  have hStep19 : Runs w p ω (.assign 19 (.load (.reg 18)))
      ⟨mem, rg18, stZero.pos⟩ .normal ⟨mem, rg19, stZero.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨vCap0, by simp [Expr.eval, rg18, hRootVC], rfl, rfl, rfl⟩
  have hStep20 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 18) (.const 1))))
      ⟨mem, rg19, stZero.pos⟩ .normal ⟨mem, rg20, stZero.pos⟩ 5 :=
    runs_assign_iff.mpr ⟨eCap0,
      by simp [Expr.eval, BinOp.eval, rg19, rg18, show 1 < 2 ^ w by omega,
        show rootGraph + 1 < 2 ^ w by omega, hRootEC], rfl, rfl, rfl⟩
  have hStep21 : Runs w p ω (.assign 21 (.bin .add (.bin .add (.reg 18) (.const 4)) (.bin .mul (.const 4) (.reg 19))))
      ⟨mem, rg20, stZero.pos⟩ .normal ⟨mem, rg21, stZero.pos⟩ 8 :=
    runs_assign_iff.mpr ⟨dgIntToExtBase rootGraph vCap0,
      by simp [Expr.eval, BinOp.eval, rg20, rg19, rg18, dgIntToExtBase, show 4 < 2 ^ w by omega,
        show rootGraph + 4 < 2 ^ w by omega, show 4 * vCap0 < 2 ^ w by omega,
        show rootGraph + 4 + 4 * vCap0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hStep22 : Runs w p ω (.assign 22 (.bin .add (.bin .add (.bin .add (.reg 18) (.const 4))
        (.bin .mul (.const 7) (.reg 19))) (.bin .mul (.const 3) (.reg 20))))
      ⟨mem, rg21, stZero.pos⟩ .normal ⟨mem, rg22, stZero.pos⟩ 12 :=
    runs_assign_iff.mpr ⟨dgETailSlotBase rootGraph vCap0 eCap0,
      by simp [Expr.eval, BinOp.eval, rg21, rg20, rg19, rg18, dgETailSlotBase,
        show 3 < 2 ^ w by omega, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
        show rootGraph + 4 < 2 ^ w by omega, show 7 * vCap0 < 2 ^ w by omega,
        show rootGraph + 4 + 7 * vCap0 < 2 ^ w by omega, show 3 * eCap0 < 2 ^ w by omega,
        show rootGraph + 4 + 7 * vCap0 + 3 * eCap0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hStep23 : Runs w p ω (.assign 23 (.bin .add (.reg 22) (.reg 20)))
      ⟨mem, rg22, stZero.pos⟩ .normal ⟨mem, rg23, stZero.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨dgEHeadSlotBase rootGraph vCap0 eCap0,
      by simp [Expr.eval, BinOp.eval, rg22, rg21, rg20, dgETailSlotBase, dgEHeadSlotBase,
        Nat.add_assoc]; omega, rfl, rfl, rfl⟩
  let c23 := 4 + c + 1; let c22 := 12 + c23 + 1; let c21 := 8 + c22 + 1
  let c20 := 5 + c21 + 1; let c19 := 3 + c20 + 1; let c18 := 5 + c19 + 1
  let c17 := 5 + c18 + 1; let c16 := 5 + c17 + 1; let c15 := 3 + c16 + 1
  let c14 := 6 + c15 + 1; let c13 := (cZero + 3) + c14 + 1; let c12 := (cNeg + 3) + c13 + 1
  let c11 := 6 + c12 + 1; let c10 := 5 + c11 + 1; let c9 := 3 + c10 + 1
  let c8 := 5 + c9 + 1; let c7 := 5 + c8 + 1; let c6 := 5 + c7 + 1
  let c5 := 5 + c6 + 1; let cCond := 3 + c5 + 1; let cTot := 3 + cCond + 1
  have hcTot : cTot ≤ T := by
    have h1 : ∀ a b c : ℕ, 3 + (3 + (5 + (5 + (5 + (5 + (3 + (5 + (6 + ((a + 3) + ((b + 3) + (6 +
      (3 + (5 + (5 + (5 + (3 + (5 + (8 + (12 + (4 + c + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
      1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = a + b + 123 + c := by
      clear hrRest hQ hcT hStep4 hStep5 hStep6 hStep7 hStep8 hStep9 hStep10 hStep11 hStep12 hStep13
        hStep14 hStep15 hStep16 hStep17 hStep18 hStep19 hStep20 hStep21 hStep22 hStep23
        rg23 rg22 rg21 rg20 rg19 rg18 rg17 rg16 rg15 rg14 rg13 rg12 rg11 rg10 rg9 rg8 rg7 rg6 rg5 rg4 s0
      intro a b c; omega
    have hEq : cTot = cNeg + cZero + 123 + c := h1 cNeg cZero c
    exact le_trans (by rw [hEq]; exact Nat.add_le_add_right (Nat.add_le_add_left (by decide : 123 ≤ 135) _) c) hcT
  have r23 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg23, stZero.pos⟩, 4, c, hStep23, hrRest, rfl⟩)
  have r22 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg22, stZero.pos⟩, 12, c23, hStep22, r23, rfl⟩)
  have r21 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg21, stZero.pos⟩, 8, c22, hStep21, r22, rfl⟩)
  have r20 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg20, stZero.pos⟩, 5, c21, hStep20, r21, rfl⟩)
  have r19 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg19, stZero.pos⟩, 3, c20, hStep19, r20, rfl⟩)
  have r18 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg18, stZero.pos⟩, 5, c19, hStep18, r19, rfl⟩)
  have r17 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg17, stZero.pos⟩, 5, c18, hStep17, r18, rfl⟩)
  have r16 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg16, stZero.pos⟩, 5, c17, hStep16, r17, rfl⟩)
  have r15 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg15, stZero.pos⟩, 3, c16, hStep15, r16, rfl⟩)
  have r14 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg14, stZero.pos⟩, 6, c15, hStep14, r15, rfl⟩)
  have r13 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg13, stZero.pos⟩, cZero + 3, c14, hStep13, r14, rfl⟩)
  have r12 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg12, stNeg.pos⟩, cNeg + 3, c13, hStep12, r13, rfl⟩)
  have r11 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg11, pos⟩, 6, c12, hStep11, r12, rfl⟩)
  have r10 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg10, pos⟩, 5, c11, hStep10, r11, rfl⟩)
  have r9 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg9, pos⟩, 3, c10, hStep9, r10, rfl⟩)
  have r8 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg8, pos⟩, 5, c9, hStep8, r9, rfl⟩)
  have r7 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg7, pos⟩, 5, c8, hStep7, r8, rfl⟩)
  have r6 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg6, pos⟩, 5, c7, hStep6, r7, rfl⟩)
  have r5 := runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg5, pos⟩, 5, c6, hStep5, r6, rfl⟩)
  refine ⟨o, st', cTot, ?_, hQ, hcTot⟩
  refine runs_seq_iff.mpr (Or.inr ⟨⟨mem, rg4, pos⟩, 3, cCond, hStep4, ?_, rfl⟩)
  exact runs_cond_iff.mpr ⟨0, c5,
    by simp [Expr.eval, BinOp.eval, rg4, hszNZ, show 0 < 2 ^ w by omega],
    r5, rfl⟩

end MinCostFlow.MinRatio
