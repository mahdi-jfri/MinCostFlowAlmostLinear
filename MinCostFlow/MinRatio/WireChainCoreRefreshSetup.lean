module

public import MinCostFlow.MinRatio.WireChainCoreRefresh
public import MinCostFlow.MinRatio.WireChainCoreLen0
import WordRAM.Tactic

/-!
# Batch edge-account refresh setup and off-ready push helper (`WireChainCoreRefreshSetup`)

Defines `wireRefreshAccountsSetup`, `wireRefreshAccountsStep`, and `wireRefreshAccountsBody`
(which refreshes `edgeThresholds[ei_new]` and `edgeRecords[ei_new]` for every live `.delete ei_old`
in `U_int` without modifying `offReadyList` or `inOffReady`), together with `offReadyInv_push` and
`wireRefreshAccountsSetup_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
  MinCostFlow.IPM.Machine

/-- Load directory/header fields and build `-ε` via `initNegEpsilonBlock`. -/
@[expose] def wireRefreshAccountsSetup (shift negate : ℕ) : Stmt :=
  .assign 60 (.reg 0) ;;
  .assign 61 (.reg 1) ;;
  .assign 62 (.reg 2) ;;
  .assign 63 (.reg 3) ;;
  .assign 99 (.reg 4) ;;
  .assign 64 (.load (.reg 60)) ;;
  .assign 65 (.load (.bin .add (.reg 60) (.const 3))) ;;
  .assign 66 (.load (.bin .add (.reg 60) (.const 4))) ;;
  .assign 67 (.load (.bin .add (.reg 64) (.const 5))) ;;
  .assign 68 (.load (.bin .add (.reg 64) (.const 8))) ;;
  .assign 69 (.load (.bin .add (.reg 60) (.const 9))) ;;
  .assign 70 (.load (.bin .add (.reg 60) (.const 10))) ;;
  .assign 73 (.load (.bin .add (.reg 64) (.const 16))) ;;
  .assign 75 (.load (.bin .add (.reg 60) (.const 14))) ;;
  .assign 76 (.load (.reg 75)) ;;
  .assign 77 (.bin .add (.bin .add (.reg 75) (.const 4)) (.bin .mul (.const 7) (.reg 76))) ;;
  initNegEpsilonBlock shift negate

/-- One loop step of `wireRefreshAccountsBody`: advance past `.insert`, or refresh a live `.delete`. -/
@[expose] def wireRefreshAccountsStep (refreshOneProc : ℕ) : Stmt :=
  .assign 81 (.load (.reg 79)) ;;
  .cond (.bin .eq (.reg 81) (.const 0))
    (.assign 79 (.bin .add (.reg 79) (.const 4)))
    (.assign 82 (.load (.bin .add (.reg 79) (.const 1))) ;;
     .assign 79 (.bin .add (.reg 79) (.const 2)) ;;
     .cond (.load (.bin .add (.reg 77) (.reg 82)))
       (.assign 83 (.load (.bin .add (.reg 66) (.reg 82))) ;;
        .assign 84 (.load (.bin .add (.reg 65) (.reg 83))) ;;
        .assign 85 (.load (.bin .add (.reg 70) (.reg 82))) ;;
        .assign 86 (.load (.bin .add (.reg 69) (.reg 82))) ;;
        .call 99 refreshOneProc
          [.reg 85, .reg 86,
           .bin .add (.reg 62) (.bin .mul (.reg 83) (.reg 67)),
           .bin .add (.reg 63) (.bin .mul (.reg 83) (.reg 67)),
           .reg 95, .reg 67, .reg 68, .reg 99] ;;
        .assign 87 (.load (.bin .sub (.reg 99) (.const 3))) ;;
        .assign 88 (.load (.bin .sub (.reg 99) (.const 2))) ;;
        .store (.bin .add (.reg 69) (.reg 84)) (.reg 87) ;;
        .store (.bin .add (.reg 70) (.reg 84)) (.reg 88))
       .nop)

/-- Procedure `[root, uIntBuf, g, l, heap]` (`regs 0..4`): refreshes `edgeThresholds[ei_new]` and
`edgeRecords[ei_new]` for all replaced edges in `U_int`, returning `nextHeap`. -/
@[expose] def wireRefreshAccountsBody (shift negate refreshOneProc : ℕ) : Stmt :=
  wireRefreshAccountsSetup shift negate ;;
  .assign 78 (.load (.reg 61)) ;;
  .assign 79 (.bin .add (.reg 61) (.const 1)) ;;
  forRange 80 (.const 0) (.reg 78) (wireRefreshAccountsStep refreshOneProc) ;;
  .ret (.reg 99)

theorem wireRefreshAccountsBody_noRand (shift negate refreshOneProc : ℕ) :
    (wireRefreshAccountsBody shift negate refreshOneProc).NoRand := by
  simp [wireRefreshAccountsBody, wireRefreshAccountsSetup, wireRefreshAccountsStep,
    initNegEpsilonBlock, forRange, forUp, Stmt.NoRand]

/-- Pushing a fresh element `ei < intCap` with `inOffReady[ei] = 0` preserves `OffReadyInv` and
guarantees `cnt < intCap`. -/
theorem wireCore_offReadyInv_push {mem : ℕ → ℕ} {cnt offList inOff intCap ei : ℕ}
    (hInv : OffReadyInv mem cnt offList inOff intCap)
    (hei : ei < intCap) (h0 : mem (inOff + ei) = 0)
    (hDisj : offList + intCap ≤ inOff ∨ inOff + intCap ≤ offList) :
    cnt < intCap ∧
    OffReadyInv
      (Function.update (Function.update mem (offList + cnt) ei) (inOff + ei) 1)
      (cnt + 1) offList inOff intCap := by
  obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hInv
  have hlt : cnt < intCap := by
    by_contra hge
    have hEq : cnt = intCap := by omega
    let f : Fin intCap → Fin intCap := fun j => ⟨mem (offList + j.val), (hmemL j.val (by omega)).1⟩
    have hfInj : Function.Injective f := fun a b hab => by
      by_contra hne
      have := hdist a.val (by omega) b.val (by omega) (fun h => hne (Fin.ext h))
      exact this (congrArg Fin.val hab)
    have hfSurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfInj
    obtain ⟨j, hj⟩ := hfSurj ⟨ei, hei⟩
    have h1 := (hmemL j.val (by omega)).2
    rw [show mem (offList + j.val) = ei from congrArg Fin.val hj] at h1
    omega
  refine ⟨hlt, by omega, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hne : offList + j ≠ inOff + ei := by rcases hDisj with h | h <;> omega
    rw [Function.update_of_ne hne]
    by_cases hjc : j = cnt
    · subst hjc; simp [hei]
    · rw [Function.update_of_ne (by omega : offList + j ≠ offList + cnt)]
      have hlj := hmemL j (by omega)
      refine ⟨hlj.1, ?_⟩
      by_cases hEq : mem (offList + j) = ei
      · rw [hEq]; simp
      · rw [Function.update_of_ne (by omega : inOff + mem (offList + j) ≠ inOff + ei),
            Function.update_of_ne (by rcases hDisj with h | h <;> omega : inOff + mem (offList + j) ≠ offList + cnt)]
        exact hlj.2
  · intro j₁ hj₁ j₂ hj₂ hne
    have h1 : offList + j₁ ≠ inOff + ei := by rcases hDisj with h | h <;> omega
    have h2 : offList + j₂ ≠ inOff + ei := by rcases hDisj with h | h <;> omega
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    by_cases h1c : j₁ = cnt
    · subst h1c
      rw [Function.update_self, Function.update_of_ne (by omega : offList + j₂ ≠ offList + j₁)]
      intro heq
      have h1' := (hmemL j₂ (by omega)).2
      rw [← heq] at h1'; omega
    · by_cases h2c : j₂ = cnt
      · subst h2c
        rw [Function.update_self, Function.update_of_ne (by omega : offList + j₁ ≠ offList + j₂)]
        intro heq
        have h1' := (hmemL j₁ (by omega)).2
        rw [heq] at h1'; omega
      · rw [Function.update_of_ne (by omega : offList + j₁ ≠ offList + cnt),
            Function.update_of_ne (by omega : offList + j₂ ≠ offList + cnt)]
        exact hdist j₁ (by omega) j₂ (by omega) hne
  · intro e he
    by_cases hee : e = ei
    · subst hee; simp
    · rw [Function.update_of_ne (by omega : inOff + e ≠ inOff + ei),
          Function.update_of_ne (by rcases hDisj with h | h <;> omega : inOff + e ≠ offList + cnt)]
      exact hbits e he
  · intro e he h1
    by_cases hee : e = ei
    · subst hee
      refine ⟨cnt, Nat.lt_succ_self cnt, ?_⟩
      rw [Function.update_of_ne (by rcases hDisj with h | h <;> omega : offList + cnt ≠ inOff + e),
          Function.update_self]
    · rw [Function.update_of_ne (by omega : inOff + e ≠ inOff + ei),
          Function.update_of_ne (by rcases hDisj with h | h <;> omega : inOff + e ≠ offList + cnt)] at h1
      obtain ⟨j, hj, hje⟩ := hrev e he h1
      refine ⟨j, Nat.lt_succ_of_lt hj, ?_⟩
      rw [Function.update_of_ne (by rcases hDisj with h | h <;> omega : offList + j ≠ inOff + ei),
          Function.update_of_ne (by omega : offList + j ≠ offList + cnt)]
      exact hje

/-- Predicate identifying the two pointer tables modified below `heap` by `wireRefreshAccountsBody`:
`edgeThresholds[0..intCap)` and `edgeRecords[0..intCap)`. -/
@[expose] def InRefreshMutable (edgeThresholds edgeRecords intCap a : ℕ) : Prop :=
  (edgeThresholds ≤ a ∧ a < edgeThresholds + intCap) ∨
  (edgeRecords ≤ a ∧ a < edgeRecords + intCap)

/-- Execute `wireRefreshAccountsSetup`: loads directory/header addresses and builds `-ε` at
`heap + 2 * L`, returning `out.regs 95 = heap + 2 * L` and `out.regs 99 = heap + 3 * L`. -/
theorem wireRefreshAccountsSetup_runs
    {w shift negate root uIntBuf g l heap handle table levelsEnd forward inverse freshCounter
      slots names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      rootGraph intCap n rootECap L P epsExp pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {G0 : MGraph}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hRoot : SolverRootDirAt mem root handle table levelsEnd forward inverse freshCounter slots
      names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      rootGraph intCap)
    (hLmem : mem (handle + 5) = L) (hPmem : mem (handle + 8) = P)
    (hEpsMem : mem (handle + 16) = epsExp)
    (hDG0 : DynGraphAt mem rootGraph n rootECap G0)
    (hLpos : 0 < L) (hPword : P < 2 ^ w) (hle : epsExp ≤ P) (hfitPos : P - epsExp + 1 < 4 * L)
    (hRootLe : root + 16 ≤ heap) (hHandleLe : handle + 18 ≤ heap)
    (hRGLe : rootGraph + dynGraphSize n rootECap ≤ heap)
    (hz : ZeroFrom mem heap) (hRoom : heap + 3 * L < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω (wireRefreshAccountsSetup shift negate)
        (startState [root, uIntBuf, g, l, heap] mem pos) .normal out cost ∧
      cost ≤ 71 * L + 170 ∧
      out.regs 60 = root ∧ out.regs 61 = uIntBuf ∧ out.regs 62 = g ∧ out.regs 63 = l ∧
      out.regs 64 = handle ∧ out.regs 65 = forward ∧ out.regs 66 = inverse ∧
      out.regs 67 = L ∧ out.regs 68 = P ∧ out.regs 69 = edgeThresholds ∧
      out.regs 70 = edgeRecords ∧ out.regs 73 = epsExp ∧ out.regs 75 = rootGraph ∧
      out.regs 76 = n ∧ out.regs 77 = rootGraph + 4 + 7 * n ∧
      out.regs 95 = heap + 2 * L ∧ out.regs 99 = heap + 3 * L ∧
      PathIntAt out.mem (heap + 2 * L) 4 L (-((2 : ℤ) ^ (P - epsExp))) ∧
      ZeroFrom out.mem (heap + 3 * L) ∧
      ∀ a < heap, out.mem a = mem a := by
  have hw1 : 1 < 2 ^ w := by omega
  have hRG0 : mem rootGraph = n := by simpa [dgVCapOff] using hDG0.2.2.2.1
  have hDGSize : 4 + 7 * n ≤ dynGraphSize n rootECap := by unfold dynGraphSize; omega
  have hEPW : rootGraph + 4 + 7 * n < 2 ^ w := by omega
  let s0 := startState [root, uIntBuf, g, l, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 60 root }
  let s2 := { s1 with regs := Function.update s1.regs 61 uIntBuf }
  let s3 := { s2 with regs := Function.update s2.regs 62 g }
  let s4 := { s3 with regs := Function.update s3.regs 63 l }
  let s5 := { s4 with regs := Function.update s4.regs 99 heap }
  let s6 := { s5 with regs := Function.update s5.regs 64 handle }
  let s7 := { s6 with regs := Function.update s6.regs 65 forward }
  let s8 := { s7 with regs := Function.update s7.regs 66 inverse }
  let s9 := { s8 with regs := Function.update s8.regs 67 L }
  let s10 := { s9 with regs := Function.update s9.regs 68 P }
  let s11 := { s10 with regs := Function.update s10.regs 69 edgeThresholds }
  let s12 := { s11 with regs := Function.update s11.regs 70 edgeRecords }
  let s13 := { s12 with regs := Function.update s12.regs 73 epsExp }
  let s14 := { s13 with regs := Function.update s13.regs 75 rootGraph }
  let s15 := { s14 with regs := Function.update s14.regs 76 n }
  let s16 := { s15 with regs := Function.update s15.regs 77 (rootGraph + 4 + 7 * n) }
  have hr1 : Runs w p ω (.assign 60 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 61 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨uIntBuf, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 62 (.reg 2)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨g, by simp [Expr.eval, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 63 (.reg 3)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨l, by simp [Expr.eval, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 99 (.reg 4)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have hr6 : Runs w p ω (.assign 64 (.load (.reg 60))) s5 .normal s6 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s5, s4, s3, s2, s1, s0, startState,
      show mem root = handle by simpa using hRoot 0 (by simp)], rfl, rfl, rfl⟩
  have hr7 : Runs w p ω (.assign 65 (.load (.bin .add (.reg 60) (.const 3)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨forward, by simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0,
      startState, show 3 < 2 ^ w by omega, show root + 3 < 2 ^ w by omega,
      show mem (root + 3) = forward by simpa using hRoot 3 (by simp)], rfl, rfl, rfl⟩
  have hr8 : Runs w p ω (.assign 66 (.load (.bin .add (.reg 60) (.const 4)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨inverse, by simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, s0,
      startState, show 4 < 2 ^ w by omega, show root + 4 < 2 ^ w by omega,
      show mem (root + 4) = inverse by simpa using hRoot 4 (by simp)], rfl, rfl, rfl⟩
  have hr9 : Runs w p ω (.assign 67 (.load (.bin .add (.reg 64) (.const 5)))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      startState, show 5 < 2 ^ w by omega, show handle + 5 < 2 ^ w by omega, hLmem], rfl, rfl, rfl⟩
  have hr10 : Runs w p ω (.assign 68 (.load (.bin .add (.reg 64) (.const 8)))) s9 .normal s10 5 :=
    runs_assign_iff.mpr ⟨P, by simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      startState, show 8 < 2 ^ w by omega, show handle + 8 < 2 ^ w by omega, hPmem], rfl, rfl, rfl⟩
  have hr11 : Runs w p ω (.assign 69 (.load (.bin .add (.reg 60) (.const 9)))) s10 .normal s11 5 :=
    runs_assign_iff.mpr ⟨edgeThresholds, by simp [Expr.eval, BinOp.eval, s10, s9, s8, s7, s6, s5,
      s4, s3, s2, s1, s0, startState, show 9 < 2 ^ w by omega, show root + 9 < 2 ^ w by omega,
      show mem (root + 9) = edgeThresholds by simpa using hRoot 9 (by simp)], rfl, rfl, rfl⟩
  have hr12 : Runs w p ω (.assign 70 (.load (.bin .add (.reg 60) (.const 10)))) s11 .normal s12 5 :=
    runs_assign_iff.mpr ⟨edgeRecords, by simp [Expr.eval, BinOp.eval, s11, s10, s9, s8, s7, s6, s5,
      s4, s3, s2, s1, s0, startState, show 10 < 2 ^ w by omega, show root + 10 < 2 ^ w by omega,
      show mem (root + 10) = edgeRecords by simpa using hRoot 10 (by simp)], rfl, rfl, rfl⟩
  have hr13 : Runs w p ω (.assign 73 (.load (.bin .add (.reg 64) (.const 16)))) s12 .normal s13 5 :=
    runs_assign_iff.mpr ⟨epsExp, by simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8, s7, s6, s5,
      s4, s3, s2, s1, s0, startState, hw16, show handle + 16 < 2 ^ w by omega, hEpsMem], rfl, rfl, rfl⟩
  have hr14 : Runs w p ω (.assign 75 (.load (.bin .add (.reg 60) (.const 14)))) s13 .normal s14 5 :=
    runs_assign_iff.mpr ⟨rootGraph, by simp [Expr.eval, BinOp.eval, s13, s12, s11, s10, s9, s8,
      s7, s6, s5, s4, s3, s2, s1, s0, startState, show 14 < 2 ^ w by omega,
      show root + 14 < 2 ^ w by omega, show mem (root + 14) = rootGraph by simpa using hRoot 14 (by simp)],
      rfl, rfl, rfl⟩
  have hr15 : Runs w p ω (.assign 76 (.load (.reg 75))) s14 .normal s15 3 :=
    runs_assign_iff.mpr ⟨n, by simp [Expr.eval, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
      s3, s2, s1, s0, startState, hRG0], rfl, rfl, rfl⟩
  have hr16 : Runs w p ω
      (.assign 77 (.bin .add (.bin .add (.reg 75) (.const 4)) (.bin .mul (.const 7) (.reg 76))))
      s15 .normal s16 8 :=
    runs_assign_iff.mpr ⟨rootGraph + 4 + 7 * n, by
      simp [Expr.eval, BinOp.eval, s15, s14, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
        show rootGraph + 4 < 2 ^ w by omega, show 7 * n < 2 ^ w by omega, hEPW], rfl, rfl, rfl⟩
  obtain ⟨out, cEps, rEps, h95, h99, hNegEps, hzOut, hFrOut, hKeepRegs, hcEps⟩ :=
    initNegEpsilonBlock_runs (w := w) (shift := shift) (negate := negate)
      (L := L) (P := P) (epsExp := epsExp) (heap := heap) (p := p) (ω := ω) (st := s16)
      hshift hneg (by simp [s16, s15, s14, s13, s12, s11, s10, s9])
      (by simp [s16, s15, s14, s13, s12, s11, s10])
      (by simp [s16, s15, s14, s13])
      (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5])
      hLpos hPword hle hfitPos hz hRoom hw1
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, hr1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, hr2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, hr3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 2, _, hr4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, hr5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 3, _, hr6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, hr7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, hr8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, hr9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 5, _, hr10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 5, _, hr11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 5, _, hr12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 5, _, hr13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 5, _, hr14,
    runs_seq_iff.mpr (Or.inr ⟨s15, 3, _, hr15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 8, cEps, hr16, rEps, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨out, _, rAll, by omega,
    (hKeepRegs 60 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]),
    (hKeepRegs 61 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]),
    (hKeepRegs 62 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3]),
    (hKeepRegs 63 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4]),
    (hKeepRegs 64 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6]),
    (hKeepRegs 65 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7]),
    (hKeepRegs 66 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9, s8]),
    (hKeepRegs 67 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10, s9]),
    (hKeepRegs 68 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11, s10]),
    (hKeepRegs 69 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12, s11]),
    (hKeepRegs 70 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13, s12]),
    (hKeepRegs 73 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14, s13]),
    (hKeepRegs 75 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15, s14]),
    (hKeepRegs 76 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16, s15]),
    (hKeepRegs 77 (by decide) (by decide) (by decide) (by decide)).trans (by simp [s16]),
    h95, h99, hNegEps, hzOut, hFrOut⟩

end MinCostFlow.MinRatio
