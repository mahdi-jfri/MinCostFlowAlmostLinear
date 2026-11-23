module

public import MinCostFlow.MinRatio.PathNormalizationProgram
public import MinCostFlow.MinRatio.PathFlowTag
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Good-cycle normalization, output header, and path-tag setup for `Update`

When `algorithm2_loopWith` finds a good cycle with negative gradient inner product
`inner = (-magnitude) / 2^P` (`0 < magnitude`), `updateGoodNormOutBody` computes:
1. the rounded `L`-limb flow multiplier `multiplier = pathMultiplier P request magnitude` and the
   exact `2L`-limb actual normalization `actual` at precision `2P` via `pathNormalizationBody`,
2. the `Update` output header at `outHeap`: `mem'[outHeap] = 1` (`AnswerAt mem' outHeap (some Δ)`)
   and `ScalarAt mem' (outHeap + 1) 4 (2 * L) (2 * P) actual` with `NormalizationWithin req actual`,
3. the `2L`-limb `PathTagAt` block `PathTag.ofFlow multiplier` at `workHeap + fixedDivideSpace L + 6 * L`
   via `pathFlowTagBody`, leaving the `L`-limb `multiplier` block intact at
   `workHeap + fixedDivideSpace L - L` for explicit off-tree edge updates.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Fixed deterministic procedure taking `[eta, magPtr, L, P, outHeap, workHeap]`.
Computes the rounded multiplier and exact actual normalization, writes the success bit `1`
at `outHeap` and the `2L`-limb actual normalization at `outHeap + 1`, builds the `PathTag`
block at `workHeap + Num.fixedDivideSpace L + 6 * L`, and returns
`workHeap + Num.fixedDivideSpace L + 8 * L`. -/
@[expose] def updateGoodNormOutBody (pathNorm copyWords pathFlowTag : ℕ) : Stmt :=
  .call 6 pathNorm [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5] ;;
  .store (.reg 4) (.const 1) ;;
  .assign 7 (.bin .mul (.const 2) (.reg 2)) ;;
  .assign 8 (.bin .sub (.reg 6) (.reg 7)) ;;
  .assign 9 (.bin .add (.reg 4) (.const 1)) ;;
  .call 10 copyWords [.reg 8, .reg 9, .reg 7] ;;
  .assign 11 (.bin .sub (.reg 6) (.bin .mul (.const 7) (.reg 2))) ;;
  .call 12 pathFlowTag [.reg 11, .reg 2, .reg 6] ;;
  .ret (.reg 12)

theorem updateGoodNormOutBody_noRand (pathNorm copyWords pathFlowTag : ℕ) :
    (updateGoodNormOutBody pathNorm copyWords pathFlowTag).NoRand := by
  simp [updateGoodNormOutBody, Stmt.NoRand]

/-- Execution and exact output/frame specification of `updateGoodNormOutBody`. -/
theorem updateGoodNormOutBody_runs
    {w pathNorm copyWords pathFlowTag eta magPtr L P outHeap workHeap pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {request magnitude : ℤ}
    (hNorm : MeetsContract w p pathNorm (pathNormalizationContract w 4 request magnitude))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hTag : MeetsContract w p pathFlowTag (pathFlowTagContract w 4 (pathMultiplier P request magnitude)))
    (hP4 : 4 ∣ P) (hPW : P < 2 ^ w) (hw7 : 7 < 2 ^ w)
    (hmagPos : 0 < magnitude)
    (hstep : (2 : ℝ) * ((magnitude : ℝ) / (2 : ℝ) ^ P) ≤ (request : ℝ))
    (hetaEnd : eta + L ≤ workHeap) (hmagEnd : magPtr + L ≤ workHeap)
    (houtEnd : outHeap + 1 + 2 * L ≤ workHeap)
    (hetaAt : PathIntAt mem eta 4 L request)
    (hmagAt : PathIntAt mem magPtr 4 L magnitude)
    (hfitMult : Num.Fits 4 L (pathMultiplier P request magnitude))
    (hfitAbs : Num.Fits 4 L |pathMultiplier P request magnitude|)
    (hz : ZeroFrom mem workHeap)
    (hroom : workHeap + Num.fixedDivideSpace L + 8 * L < 2 ^ w) :
    let mult := pathMultiplier P request magnitude
    let req := (request : ℝ) / (2 : ℝ) ^ P
    let inner := ((-magnitude : ℤ) : ℝ) / (2 : ℝ) ^ P
    let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * inner)
    let multPtr := workHeap + Num.fixedDivideSpace L - L
    let tagPtr := workHeap + Num.fixedDivideSpace L + 6 * L
    let ret := workHeap + Num.fixedDivideSpace L + 8 * L
    ∃ cost out,
      Runs w p ω (updateGoodNormOutBody pathNorm copyWords pathFlowTag)
        (startState [eta, magPtr, L, P, outHeap, workHeap] mem pos) (.returned ret) out cost ∧
      cost ≤ 2852 * L ^ 2 + 3109 * L + 980 ∧
      out.mem outHeap = 1 ∧
      ScalarAt out.mem (outHeap + 1) 4 (2 * L) (2 * P) actual ∧
      NormalizationWithin req actual ∧
      PathIntAt out.mem multPtr 4 L mult ∧
      PathTagAt out.mem tagPtr 4 L (PathTag.ofFlow mult) ∧
      ZeroFrom out.mem ret ∧
      (∀ a < workHeap, (a < outHeap ∨ outHeap + 1 + 2 * L ≤ a) → out.mem a = mem a) := by
  dsimp only
  let mult := pathMultiplier P request magnitude
  let req := (request : ℝ) / (2 : ℝ) ^ P
  let inner := ((-magnitude : ℤ) : ℝ) / (2 : ℝ) ^ P
  let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * inner)
  let normRet := workHeap + Num.fixedDivideSpace L + 6 * L
  let multPtr := workHeap + Num.fixedDivideSpace L - L
  let ret := workHeap + Num.fixedDivideSpace L + 8 * L
  have hdivSp : L ≤ Num.fixedDivideSpace L := by unfold Num.fixedDivideSpace; omega
  have h7LW : 7 * L < 2 ^ w := by omega
  have h2LW : 2 * L < 2 ^ w := by omega
  have hnormRetW : normRet < 2 ^ w := by dsimp only [normRet]; omega
  have hmultSub : normRet - 7 * L = multPtr := by dsimp only [normRet, multPtr]; omega
  let s0 := startState [eta, magPtr, L, P, outHeap, workHeap] mem pos
  -- Step 1: call `pathNorm [eta, magPtr, L, P, workHeap]`
  obtain ⟨bN, hbN, oN, stN, cN, hrN, hpN, hcN⟩ :=
    hNorm [eta, magPtr, L, P, workHeap] mem pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨eta, magPtr, L, P, workHeap, rfl, hP4, hetaEnd, hmagEnd, hmagPos, hetaAt, hmagAt,
        hfitMult, hz, by omega⟩
  have hOutN := pathNormalization_output hmagPos hstep hpN
  obtain ⟨_, _, _, _, _, hargsN, hretN, hmultAt1, hactAt1, hfrN, hzN⟩ := hpN
  simp only [List.cons.injEq, and_true] at hargsN
  rcases hargsN with ⟨rfl, rfl, rfl, rfl, rfl⟩
  change oN.value = normRet at hretN
  change cN ≤ 2852 * L ^ 2 + 3022 * L + 830 at hcN
  let s1 : State := { regs := Function.update s0.regs 6 normRet, mem := stN.mem, pos := stN.pos }
  have r1 : Runs w p ω (.call 6 pathNorm [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5]) s0 .normal s1 (cN + 6) :=
    runs_call_iff.mpr ⟨[eta, magPtr, L, P, workHeap], bN, oN, stN, cN,
      by simp [evalArgs, Expr.eval, s0, startState], hbN, hrN,
      rfl, by simp [s1, hretN], by simp [argsSize, Expr.size]; omega⟩
  -- Step 2: store `1` at `outHeap`
  let s2 : State := { s1 with mem := Function.update s1.mem outHeap 1 }
  have r2 : Runs w p ω (.store (.reg 4) (.const 1)) s1 .normal s2 3 :=
    runs_store_iff.mpr ⟨outHeap, 1, by simp [Expr.eval, s1, s0, startState],
      by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Step 3: compute `2 * L`, `normRet - 2 * L`, `outHeap + 1`, and copy `actual`
  let s3 : State := { s2 with regs := Function.update s2.regs 7 (2 * L) }
  let s4 : State := { s3 with regs := Function.update s3.regs 8 (normRet - 2 * L) }
  let s5 : State := { s4 with regs := Function.update s4.regs 9 (outHeap + 1) }
  have r3 : Runs w p ω (.assign 7 (.bin .mul (.const 2) (.reg 2))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨2 * L, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 2 < 2 ^ w by omega, h2LW],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 8 (.bin .sub (.reg 6) (.reg 7))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨normRet - 2 * L, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, show normRet - 2 * L < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 9 (.bin .add (.reg 4) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨outHeap + 1, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, show 1 < 2 ^ w by omega,
        show outHeap + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨bC, hbC, oC, stC, cC, hrC, ⟨_, _, _, hargsC, _, hcpC, hfrC⟩, hcC⟩ :=
    hCopy [normRet - 2 * L, outHeap + 1, 2 * L] s5.mem s5.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> omega)
      ⟨normRet - 2 * L, outHeap + 1, 2 * L, rfl, by omega, by omega, by omega,
        Or.inl (by dsimp only [normRet]; omega)⟩
  simp only [List.cons.injEq, and_true] at hargsC
  rcases hargsC with ⟨rfl, rfl, rfl⟩
  change cC ≤ 17 * (2 * L) + 10 at hcC
  let s6 : State := { regs := Function.update s5.regs 10 oC.value, mem := stC.mem, pos := stC.pos }
  have r6 : Runs w p ω (.call 10 copyWords [.reg 8, .reg 9, .reg 7]) s5 .normal s6 (cC + 4) :=
    runs_call_iff.mpr ⟨[normRet - 2 * L, outHeap + 1, 2 * L], bC, oC, stC, cC,
      by simp [evalArgs, Expr.eval, s5, s4, s3], hbC, hrC, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hs6_geWork (a : ℕ) (ha : workHeap ≤ a) : s6.mem a = stN.mem a := by
    have h1 : stC.mem a = s5.mem a := hfrC a (Or.inr (by omega))
    have h2 : s5.mem a = stN.mem a := by
      dsimp only [s5, s4, s3, s2, s1]
      rw [Function.update_of_ne (show a ≠ outHeap by omega)]
    exact h1.trans h2
  -- Step 4: compute `multPtr = normRet - 7 * L` and call `pathFlowTag [multPtr, L, normRet]`
  let s7 : State := { s6 with regs := Function.update s6.regs 11 multPtr }
  have r7 : Runs w p ω (.assign 11 (.bin .sub (.reg 6) (.bin .mul (.const 7) (.reg 2)))) s6 .normal s7 6 :=
    runs_assign_iff.mpr ⟨multPtr, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState, hw7, h7LW,
        hmultSub, show multPtr < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hmultAt7 : PathIntAt s7.mem multPtr 4 L mult :=
    hmultAt1.congr (fun i hi => hs6_geWork (multPtr + i) (by dsimp only [multPtr]; omega))
  have hz7 : ZeroFrom s7.mem normRet := fun a ha =>
    (hs6_geWork a (by dsimp only [normRet] at ha; omega)).trans (hzN a (hretN.symm ▸ ha))
  obtain ⟨bT, hbT, oT, stT, cT, hrT, ⟨hretT, htagAt, hfrT, hzT⟩, hcT⟩ :=
    hTag [multPtr, L, normRet] s7.mem s7.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> omega)
      ⟨multPtr, L, normRet, rfl, by dsimp only [multPtr, normRet]; omega,
        hmultAt7, hfitAbs, hz7, by dsimp only [normRet]; omega⟩
  change oT.value = normRet + 2 * L at hretT
  change PathTagAt stT.mem normRet 4 L (PathTag.ofFlow mult) at htagAt
  change ∀ x < normRet, stT.mem x = s7.mem x at hfrT
  change cT ≤ 53 * L + 64 at hcT
  have hretTeq : oT.value = ret := by rw [hretT]; dsimp only [normRet, ret]; omega
  let out : State := { regs := Function.update s7.regs 12 ret, mem := stT.mem, pos := stT.pos }
  have r8 : Runs w p ω (.call 12 pathFlowTag [.reg 11, .reg 2, .reg 6]) s7 .normal out (cT + 4) :=
    runs_call_iff.mpr ⟨[multPtr, L, normRet], bT, oT, stT, cT,
      by simp [evalArgs, Expr.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState],
      hbT, hrT, rfl, by simp [out, hretTeq], by simp [argsSize, Expr.size]; omega⟩
  have r9 : Runs w p ω (.ret (.reg 12)) out (.returned ret) out 2 :=
    runs_ret_iff.mpr ⟨ret, by simp [Expr.eval, out], rfl, rfl, rfl⟩
  have hrFull : Runs w p ω (updateGoodNormOutBody pathNorm copyWords pathFlowTag) s0
      (.returned ret) out
      ((cN + 6) + (3 + (4 + (4 + (4 + ((cC + 4) + (6 + ((cT + 4) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, cN + 6, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 4, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, cC + 4, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 6, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨out, cT + 4, 2, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Verify outputs in `out.mem = stT.mem`
  have hout1 : out.mem outHeap = 1 := by
    change stT.mem outHeap = 1
    rw [hfrT outHeap (by dsimp only [normRet]; omega)]
    change stC.mem outHeap = 1
    rw [hfrC outHeap (Or.inl (by omega))]
    simp [s5, s4, s3, s2]
  have houtScalar : ScalarAt out.mem (outHeap + 1) 4 (2 * L) (2 * P) actual := by
    have hag : ∀ i < 2 * L, out.mem (outHeap + 1 + i) = stN.mem (normRet - 2 * L + i) := fun i hi => by
      change stT.mem (outHeap + 1 + i) = stN.mem (normRet - 2 * L + i)
      rw [hfrT (outHeap + 1 + i) (by dsimp only [normRet]; omega)]
      change stC.mem (outHeap + 1 + i) = stN.mem (normRet - 2 * L + i)
      rw [hcpC i hi]
      dsimp only [s5, s4, s3, s2, s1]
      rw [Function.update_of_ne (show normRet - 2 * L + i ≠ outHeap by dsimp only [normRet]; omega)]
    have hscN : ScalarAt stN.mem (normRet - 2 * L) 4 (2 * L) (2 * P) actual := by
      simpa only [hretN] using hOutN.1
    refine ⟨fun i hi => by rw [hag i hi]; exact hscN.1 i hi, ?_⟩
    rw [Num.fixVal, Num.intVal, Num.unsignedVal_congr (fun i hi => hag i hi)]
    exact hscN.2
  have houtMult : PathIntAt out.mem multPtr 4 L mult :=
    hmultAt7.congr (fun i hi => hfrT (multPtr + i) (by dsimp only [multPtr, normRet]; omega))
  refine ⟨_, out, hrFull, by omega, hout1, houtScalar, hOutN.2, houtMult, htagAt,
    by change ZeroFrom stT.mem ret; rw [← hretTeq]; exact hzT, fun a ha hnotOut => ?_⟩
  change stT.mem a = mem a
  rw [hfrT a (by dsimp only [normRet]; omega)]
  change stC.mem a = mem a
  rw [hfrC a (by omega)]
  dsimp only [s5, s4, s3, s2, s1]
  rw [Function.update_of_ne (by omega)]
  exact hfrN a ha

end MinCostFlow.MinRatio
