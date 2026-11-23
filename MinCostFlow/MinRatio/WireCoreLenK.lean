module

public import MinCostFlow.MinRatio.Layouts
public import MinCostFlow.Num.SignExtend
public import MinCostFlow.Num.Multiply
public import MinCostFlow.Num.IntegerDivide
public import WordRAM.CopyWords
public import MinCostFlow.Chain.CoreGraph
import MinCostFlow.Num.DivisionSigns
import MinCostFlow.Num.RoundingFacts
import MinCostFlow.Num.ShiftFacts
import WordRAM.Tactic

/-!
# Computing `coreLen` for the sparse-core contract (`L_w`-limb stretch ratios)

Under `sparseCoreOrdMachineContractK`, and so under `sparseCoreOrdMachineContractKFBL`, operation
`2` (`readLSF`) writes `LSFAt` whose stretch
descriptor `StretchValuesAt` uses `L_w` limbs (`L_w ≤ L + capExp * (Nat.log 2 (M + N + 2) + 1)`)
and arbitrary positive fixed-point denominators `D_e`, rather than assuming `L_w = L` and `D_e = ℓ_e`.

This file provides a deterministic Word-RAM procedure `wireCoreLenBody` (built from
`wireCoreLenEdgeBody`) that computes `EdgeValuesAt` of `coreLen forest ℓ` in `L` limbs for every
edge `e ∈ H.E`:
1. Let `K = max L L_w`. Sign-extend `N_e` (`L_w` limbs) and `L_e` (`L` limbs) to `K` limbs
   (`Num.signExtend`), multiply into `2 * K` limbs (`Num.multiply`), sign-extend `D_e` (`L_w`
   limbs) to `2 * K` limbs (`Num.signExtend`), compute exact floor quotient `Q_e = ⌊(N_e * L_e) / D_e⌋`
   in `2 * K` limbs (`Num.integerDivide`), and copy its low `L` limbs to `outPtr + e * L`.
2. When `coreLen forest ℓ e` is representable in `(4, L, P)` fixed-point (`∃ q, Fits 4 L q ∧
   q / 2^P = coreLen forest ℓ e`), `N_e * L_e = D_e * q` holds exactly in `ℤ`, so the truncated
   low `L` limbs recover `coreLen forest ℓ e` with zero rounding error.
3. Space is `ecH * L + H.m * wireCoreLenEdgeSpace (max L L_w)` and cost is
   `O(H.m * (max L L_w)^2)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program

/-! ### Space and cost bounds -/

/-- Scratch words allocated by `wireCoreLenEdgeBody` for `K = max L L_w`. -/
@[expose] def wireCoreLenEdgeSpace (K : ℕ) : ℕ :=
  10 * K + Num.integerDivideSpace (2 * K)

/-- Step-count bound for one edge in `wireCoreLenEdgeBody` with `K = max L L_w`. -/
@[expose] def wireCoreLenEdgeCost (K : ℕ) : ℕ :=
  1400 * K ^ 2 + 2100 * K + 850

/-! ### Word-RAM procedures -/

/-- Per-edge `coreLen` procedure taking `[numPtr, denPtr, lenPtr, outPtr, e, L, Lw, heap]`
(`reg 0..7`) and returning `nextHeap = heap + wireCoreLenEdgeSpace (max L Lw)`. -/
@[expose] def wireCoreLenEdgeBody (signExt mul intDiv copy : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 5) (.reg 6))
    (.assign 8 (.reg 6))
    (.assign 8 (.reg 5)) ;;
  .assign 9 (.bin .mul (.const 2) (.reg 8)) ;;
  .assign 10 (.bin .add (.reg 0) (.bin .mul (.reg 4) (.reg 6))) ;;
  .assign 11 (.bin .add (.reg 2) (.bin .mul (.reg 4) (.reg 5))) ;;
  .assign 12 (.bin .add (.reg 1) (.bin .mul (.reg 4) (.reg 6))) ;;
  .call 13 signExt [.reg 10, .reg 6, .reg 8, .reg 7] ;;
  .call 14 signExt [.reg 11, .reg 5, .reg 8, .reg 13] ;;
  .call 15 mul [.reg 7, .reg 13, .reg 8, .reg 14] ;;
  .call 16 signExt [.reg 12, .reg 6, .reg 9, .reg 15] ;;
  .call 17 intDiv [.bin .add (.reg 14) (.bin .mul (.const 4) (.reg 8)), .reg 15, .reg 9, .reg 16] ;;
  .call 18 copy [.bin .sub (.reg 17) (.reg 9), .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5] ;;
  .ret (.reg 17)

theorem wireCoreLenEdgeBody_noRand (signExt mul intDiv copy : ℕ) :
    (wireCoreLenEdgeBody signExt mul intDiv copy).NoRand := by
  simp [wireCoreLenEdgeBody, Stmt.NoRand]

/-- Full `coreLen` table builder taking `[hBase, stretchDesc, lenPtr, L, Lw, heap]` (`reg 0..5`),
writing `EdgeValuesAt` of `coreLen forest ℓ` at `heap` (`ecH * L` words) and returning
`nextHeap = heap + ecH * L + H.m * wireCoreLenEdgeSpace (max L Lw)`. -/
@[expose] def wireCoreLenBody (edgeProc : ℕ) : Stmt :=
  .assign 6 (.load (.reg 0)) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 9 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 6))) (.reg 7)) ;;
  .assign 10 (.load (.reg 1)) ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 12 (.bin .add (.reg 5) (.bin .mul (.reg 7) (.reg 3))) ;;
  .loop (.reg 8)
    (.assign 13 (.load (.reg 9)) ;;
     .call 12 edgeProc [.reg 10, .reg 11, .reg 2, .reg 5, .reg 13, .reg 3, .reg 4, .reg 12] ;;
     .assign 9 (.bin .add (.reg 9) (.const 1)) ;;
     .assign 8 (.bin .sub (.reg 8) (.const 1))) ;;
  .ret (.reg 12)

theorem wireCoreLenBody_noRand (edgeProc : ℕ) : (wireCoreLenBody edgeProc).NoRand := by
  simp [wireCoreLenBody, Stmt.NoRand]

/-! ### Exact integer quotient bridge -/

private theorem coreLen_floorDiv_eq {P : ℕ} {N D L_e q : ℤ} {wstr ℓe : ℝ}
    (hDpos : (0 : ℝ) < (D : ℝ) / (2 : ℝ) ^ P)
    (hwstr : ((N : ℝ) / (2 : ℝ) ^ P) / ((D : ℝ) / (2 : ℝ) ^ P) = wstr)
    (hℓe : (L_e : ℝ) / (2 : ℝ) ^ P = ℓe)
    (hq : (q : ℝ) / (2 : ℝ) ^ P = wstr * ℓe) :
    0 < D ∧ Num.floorDiv (N * L_e) D = q := by
  have h2P : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos (by norm_num) P
  have hDR : (0 : ℝ) < (D : ℝ) := by
    have := mul_pos hDpos h2P; rwa [div_mul_cancel₀ _ (ne_of_gt h2P)] at this
  have hD : 0 < D := by exact_mod_cast hDR
  have hdiv : (N : ℝ) / (D : ℝ) = wstr := by
    rw [← hwstr]; field_simp [ne_of_gt h2P, ne_of_gt hDR]
  have hR : ((q * D : ℤ) : ℝ) = ((N * L_e : ℤ) : ℝ) := by
    push_cast
    have h1 : (q : ℝ) = wstr * (L_e : ℝ) := by
      have := congrArg (· * (2 : ℝ) ^ P) hq
      rw [div_mul_cancel₀ _ (ne_of_gt h2P), ← hℓe] at this
      calc (q : ℝ) = wstr * ((L_e : ℝ) / (2 : ℝ) ^ P) * (2 : ℝ) ^ P := this
        _ = wstr * (L_e : ℝ) := by field_simp [ne_of_gt h2P]
    rw [h1, ← hdiv]; field_simp [ne_of_gt hDR]
  have hZ : q * D = N * L_e := Int.cast_injective hR
  refine ⟨hD, ?_⟩
  simp only [Num.floorDiv, show ¬ D < 0 by omega, ↓reduceIte]
  rw [← hZ, Int.mul_ediv_cancel _ (by omega)]

/-! ### Per-edge execution theorem -/

/-- Execution theorem for `wireCoreLenEdgeBody`. -/
theorem wireCoreLenEdge_runs
    {w L Lw P numPtr denPtr lenPtr outPtr e heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    {signExt mul intDiv copy : ℕ} {forest : LSF} {ℓ : ℕ → ℝ} {q : ℤ}
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hNumV : Num.Valid mem (numPtr + e * Lw) 4 Lw)
    (hDenV : Num.Valid mem (denPtr + e * Lw) 4 Lw)
    (hLenV : Num.Valid mem (lenPtr + e * L) 4 L)
    (hDenPos : 0 < Num.fixVal mem (denPtr + e * Lw) 4 Lw P)
    (hWstr : Num.fixVal mem (numPtr + e * Lw) 4 Lw P /
      Num.fixVal mem (denPtr + e * Lw) 4 Lw P = forest.wstr e)
    (hLenEq : Num.fixVal mem (lenPtr + e * L) 4 L P = ℓ e)
    (hqFits : Num.Fits 4 L q)
    (hqVal : (q : ℝ) / (2 : ℝ) ^ P = coreLen forest ℓ e)
    (hNumLe : numPtr + e * Lw + Lw ≤ heap)
    (hDenLe : denPtr + e * Lw + Lw ≤ heap)
    (hLenLe : lenPtr + e * L + L ≤ heap)
    (hOutLe : outPtr + e * L + L ≤ heap)
    (hz : ZeroFrom mem heap)
    (hRoom : heap + wireCoreLenEdgeSpace (max L Lw) < 2 ^ w)
    (hw4 : 4 < 2 ^ w) :
    let K := max L Lw
    let nextHeap := heap + wireCoreLenEdgeSpace K
    ∃ out cost, Runs w p ω (wireCoreLenEdgeBody signExt mul intDiv copy)
        (startState [numPtr, denPtr, lenPtr, outPtr, e, L, Lw, heap] mem pos)
        (.returned nextHeap) out cost ∧
      cost ≤ wireCoreLenEdgeCost K ∧
      Num.Valid out.mem (outPtr + e * L) 4 L ∧
      Num.fixVal out.mem (outPtr + e * L) 4 L P = coreLen forest ℓ e ∧
      ZeroFrom out.mem nextHeap ∧
      ∀ a < heap, (a < outPtr + e * L ∨ outPtr + e * L + L ≤ a) → out.mem a = mem a := by
  intro K nextHeap
  have hLK : L ≤ K := le_max_left L Lw
  have hLwK : Lw ≤ K := le_max_right L Lw
  have hIntDivSp : Num.integerDivideSpace (2 * K) = Num.unsignedDivideSpace (2 * K) + 3 * (2 * K) := rfl
  have hKW : K < 2 ^ w := by unfold wireCoreLenEdgeSpace at hRoom; omega
  have h2KW : 2 * K < 2 ^ w := by unfold wireCoreLenEdgeSpace at hRoom; omega
  have h4KW : 4 * K < 2 ^ w := by unfold wireCoreLenEdgeSpace at hRoom; omega
  have hLW : L < 2 ^ w := by omega
  have hLwW : Lw < 2 ^ w := by omega
  have heLwW : e * Lw < 2 ^ w := by omega
  have heLW : e * L < 2 ^ w := by omega
  have hnumA : numPtr + e * Lw < 2 ^ w := by omega
  have hdenA : denPtr + e * Lw < 2 ^ w := by omega
  have hlenA : lenPtr + e * L < 2 ^ w := by omega
  have houtA : outPtr + e * L < 2 ^ w := by omega
  have hheapW : heap < 2 ^ w := by omega
  obtain ⟨hDpos, hFdiv⟩ := coreLen_floorDiv_eq (P := P) hDenPos hWstr hLenEq hqVal
  set N := Num.intVal mem (numPtr + e * Lw) 4 Lw
  set D := Num.intVal mem (denPtr + e * Lw) 4 Lw
  set Le := Num.intVal mem (lenPtr + e * L) 4 L
  -- Step 0: compute `K = max L Lw` into reg 8, `2 * K` into reg 9, addresses into regs 10..12
  let s0 := startState [numPtr, denPtr, lenPtr, outPtr, e, L, Lw, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 8 K }
  have r1 : Runs w p ω (.cond (.bin .lt (.reg 5) (.reg 6)) (.assign 8 (.reg 6)) (.assign 8 (.reg 5)))
      s0 .normal s1 6 := by
    by_cases hlt : L < Lw
    · have hK : K = Lw := max_eq_right (le_of_lt hlt)
      refine runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, BinOp.eval, s0, startState, hlt,
        show (1 : ℕ) < 2 ^ w by omega], ?_, by simp [Expr.size]⟩
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
      exact runs_assign_iff.mpr ⟨K, by simp [Expr.eval, s0, startState, hK], rfl, rfl, rfl⟩
    · have hK : K = L := max_eq_left (Nat.le_of_not_lt hlt)
      refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s0, startState, hlt,
        show (0 : ℕ) < 2 ^ w by omega], ?_, by simp [Expr.size]⟩
      simp only [↓reduceIte]
      exact runs_assign_iff.mpr ⟨K, by simp [Expr.eval, s0, startState, hK], rfl, rfl, rfl⟩
  let s2 := { s1 with regs := Function.update s1.regs 9 (2 * K) }
  let s3 := { s2 with regs := Function.update s2.regs 10 (numPtr + e * Lw) }
  let s4 := { s3 with regs := Function.update s3.regs 11 (lenPtr + e * L) }
  let s5 := { s4 with regs := Function.update s4.regs 12 (denPtr + e * Lw) }
  have r2 : Runs w p ω (.assign 9 (.bin .mul (.const 2) (.reg 8))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨2 * K, by simp [Expr.eval, BinOp.eval, s1, show 2 < 2 ^ w by omega, h2KW], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 10 (.bin .add (.reg 0) (.bin .mul (.reg 4) (.reg 6)))) s2 .normal s3 6 :=
    runs_assign_iff.mpr ⟨numPtr + e * Lw, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState,
      heLwW, hnumA], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 11 (.bin .add (.reg 2) (.bin .mul (.reg 4) (.reg 5)))) s3 .normal s4 6 :=
    runs_assign_iff.mpr ⟨lenPtr + e * L, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState,
      heLW, hlenA], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 12 (.bin .add (.reg 1) (.bin .mul (.reg 4) (.reg 6)))) s4 .normal s5 6 :=
    runs_assign_iff.mpr ⟨denPtr + e * Lw, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState,
      heLwW, hdenA], rfl, rfl, rfl⟩
  -- Call 1: `signExt [numPtr + e * Lw, Lw, K, heap]` -> `h1 = heap + K`
  have h1W : heap + K < 2 ^ w := by unfold wireCoreLenEdgeSpace at hRoom; omega
  obtain ⟨s6, c1, r1v, rc1, hp1, hr6_13, hs6Regs, hc1⟩ :=
    runs_call_of_meetsContract (r := 13) (args := [.reg 10, .reg 6, .reg 8, .reg 7])
      hSign (st := s5) (vs := [numPtr + e * Lw, Lw, K, heap])
      (by simp [evalArgs, Expr.eval, s5, s4, s3, s2, s1, s0, startState])
      (by simp [hnumA, hLwW, hKW, hheapW])
      ⟨⟨numPtr + e * Lw, Lw, K, heap, rfl, hLwK, hNumLe, hNumV⟩, hz, h1W⟩ ω
  obtain ⟨hr1v, _, _, hFr1, hz1, hExtNV, hExtNEq⟩ := hp1
  change r1v = heap + K at hr1v; subst hr1v
  change ∀ a < heap, s6.mem a = mem a at hFr1
  change ZeroFrom s6.mem (heap + K) at hz1
  change Num.Valid s6.mem heap 4 K at hExtNV
  change Num.intVal s6.mem heap 4 K = N at hExtNEq
  -- Call 2: `signExt [lenPtr + e * L, L, K, heap + K]` -> `h2 = heap + 2 * K`
  have h2W : heap + K + K < 2 ^ w := by unfold wireCoreLenEdgeSpace at hRoom; omega
  have hLenV1 : Num.Valid s6.mem (lenPtr + e * L) 4 L := fun i hi => by
    rw [hFr1 _ (by omega)]; exact hLenV i hi
  have hLenEq1 : Num.intVal s6.mem (lenPtr + e * L) 4 L = Le :=
    Num.intVal_congr (fun i hi => hFr1 _ (by omega))
  obtain ⟨s7, c2, r2v, rc2, hp2, hr7_14, hs7Regs, hc2⟩ :=
    runs_call_of_meetsContract (r := 14) (args := [.reg 11, .reg 5, .reg 8, .reg 13])
      hSign (st := s6) (vs := [lenPtr + e * L, L, K, heap + K])
      (by simp [evalArgs, Expr.eval, hr6_13, hs6Regs 11 (by decide), hs6Regs 5 (by decide),
        hs6Regs 8 (by decide), s5, s4, s3, s2, s1, s0, startState])
      (by simp [hlenA, hLW, hKW, h1W])
      ⟨⟨lenPtr + e * L, L, K, heap + K, rfl, hLK, by omega, hLenV1⟩, hz1, h2W⟩ ω
  obtain ⟨hr2v, _, _, hFr2, hz2, hExtLV, hExtLEq⟩ := hp2
  change r2v = heap + K + K at hr2v; subst hr2v
  change ∀ a < heap + K, s7.mem a = s6.mem a at hFr2
  change ZeroFrom s7.mem (heap + K + K) at hz2
  change Num.Valid s7.mem (heap + K) 4 K at hExtLV
  change Num.intVal s7.mem (heap + K) 4 K = Num.intVal s6.mem (lenPtr + e * L) 4 L at hExtLEq
  rw [hLenEq1] at hExtLEq
  -- Call 3: `mul [heap, heap + K, K, heap + 2 * K]` -> `h3 = heap + 8 * K`, prod at `heap + 6 * K`
  have h3W : heap + K + K + 6 * K < 2 ^ w := by unfold wireCoreLenEdgeSpace at hRoom; omega
  have hExtNV2 : Num.Valid s7.mem heap 4 K := fun i hi => by rw [hFr2 _ (by omega)]; exact hExtNV i hi
  have hExtNEq2 : Num.intVal s7.mem heap 4 K = N := (Num.intVal_congr (fun i hi => hFr2 _ (by omega))).trans hExtNEq
  obtain ⟨s8, c3, r3v, rc3, hp3, hr8_15, hs8Regs, hc3⟩ :=
    runs_call_of_meetsContract (r := 15) (args := [.reg 7, .reg 13, .reg 8, .reg 14])
      hMul (st := s7) (vs := [heap, heap + K, K, heap + K + K])
      (by simp [evalArgs, Expr.eval, hr7_14, hs7Regs 7 (by decide), hs7Regs 13 (by decide),
        hs7Regs 8 (by decide), hr6_13, hs6Regs 7 (by decide), hs6Regs 8 (by decide),
        s5, s4, s3, s2, s1, s0, startState])
      (by simp [hheapW, h1W, hKW, h2W])
      ⟨⟨heap, heap + K, K, heap + K + K, rfl, by omega, by omega, hExtNV2, hExtLV⟩, hz2, h3W⟩ ω
  obtain ⟨hr3v, _, _, hFr3, hz3, hProdV, hProdEq⟩ := hp3
  change r3v = heap + K + K + 6 * K at hr3v; subst hr3v
  change ∀ a < heap + K + K, s8.mem a = s7.mem a at hFr3
  change ZeroFrom s8.mem (heap + K + K + 6 * K) at hz3
  change Num.Valid s8.mem (heap + K + K + 4 * K) 4 (2 * K) at hProdV
  change Num.intVal s8.mem (heap + K + K + 4 * K) 4 (2 * K) =
    Num.intVal s7.mem heap 4 K * Num.intVal s7.mem (heap + K) 4 K at hProdEq
  rw [hExtNEq2, hExtLEq] at hProdEq
  -- Call 4: `signExt [denPtr + e * Lw, Lw, 2 * K, heap + 8 * K]` -> `h4 = heap + 10 * K`
  have h4W : heap + K + K + 6 * K + 2 * K < 2 ^ w := by unfold wireCoreLenEdgeSpace at hRoom; omega
  have hDenV3 : Num.Valid s8.mem (denPtr + e * Lw) 4 Lw := fun i hi => by
    rw [hFr3 _ (by omega), hFr2 _ (by omega), hFr1 _ (by omega)]; exact hDenV i hi
  have hDenEq3 : Num.intVal s8.mem (denPtr + e * Lw) 4 Lw = D :=
    Num.intVal_congr (fun i hi => by rw [hFr3 _ (by omega), hFr2 _ (by omega), hFr1 _ (by omega)])
  obtain ⟨s9, c4, r4v, rc4, hp4, hr9_16, hs9Regs, hc4⟩ :=
    runs_call_of_meetsContract (r := 16) (args := [.reg 12, .reg 6, .reg 9, .reg 15])
      hSign (st := s8) (vs := [denPtr + e * Lw, Lw, 2 * K, heap + K + K + 6 * K])
      (by simp [evalArgs, Expr.eval, hr8_15, hs8Regs 12 (by decide), hs8Regs 6 (by decide),
        hs8Regs 9 (by decide), hs7Regs 12 (by decide), hs7Regs 6 (by decide), hs7Regs 9 (by decide),
        hs6Regs 12 (by decide), hs6Regs 6 (by decide), hs6Regs 9 (by decide),
        s5, s4, s3, s2, s1, s0, startState])
      (by simp [hdenA, hLwW, h2KW, h3W])
      ⟨⟨denPtr + e * Lw, Lw, 2 * K, heap + K + K + 6 * K, rfl, by omega, by omega, hDenV3⟩, hz3, h4W⟩ ω
  obtain ⟨hr4v, _, _, hFr4, hz4, hExtDV, hExtDEq⟩ := hp4
  change r4v = heap + K + K + 6 * K + 2 * K at hr4v; subst hr4v
  change ∀ a < heap + K + K + 6 * K, s9.mem a = s8.mem a at hFr4
  change ZeroFrom s9.mem (heap + K + K + 6 * K + 2 * K) at hz4
  change Num.Valid s9.mem (heap + K + K + 6 * K) 4 (2 * K) at hExtDV
  change Num.intVal s9.mem (heap + K + K + 6 * K) 4 (2 * K) =
    Num.intVal s8.mem (denPtr + e * Lw) 4 Lw at hExtDEq
  rw [hDenEq3] at hExtDEq
  -- Call 5: `intDiv [heap + 6 * K, heap + 8 * K, 2 * K, heap + 10 * K]` -> `nextHeap`
  have h5Eq : heap + K + K + 6 * K + 2 * K + Num.integerDivideSpace (2 * K) = nextHeap := by
    dsimp only [nextHeap, wireCoreLenEdgeSpace]; omega
  have h5W : heap + K + K + 6 * K + 2 * K + Num.integerDivideSpace (2 * K) < 2 ^ w := by
    rw [h5Eq]; exact hRoom
  have hProdV4 : Num.Valid s9.mem (heap + K + K + 4 * K) 4 (2 * K) := fun i hi => by
    rw [hFr4 _ (by omega)]; exact hProdV i hi
  have hProdEq4 : Num.intVal s9.mem (heap + K + K + 4 * K) 4 (2 * K) = N * Le :=
    (Num.intVal_congr (fun i hi => hFr4 _ (by omega))).trans hProdEq
  have hprodPtrW : heap + K + K + 4 * K < 2 ^ w := by omega
  obtain ⟨s10, c5, r5v, rc5, hp5, hr10_17, hs10Regs, hc5⟩ :=
    runs_call_of_meetsContract (r := 17)
      (args := [.bin .add (.reg 14) (.bin .mul (.const 4) (.reg 8)), .reg 15, .reg 9, .reg 16])
      hDiv (st := s9)
      (vs := [heap + K + K + 4 * K, heap + K + K + 6 * K, 2 * K, heap + K + K + 6 * K + 2 * K])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hr9_16, hs9Regs 14 (by decide), hs9Regs 8 (by decide),
        hs9Regs 15 (by decide), hs9Regs 9 (by decide), hr8_15, hs8Regs 14 (by decide),
        hs8Regs 8 (by decide), hs8Regs 9 (by decide), hr7_14, hs7Regs 8 (by decide),
        hs7Regs 9 (by decide), hs6Regs 8 (by decide), hs6Regs 9 (by decide),
        s5, s4, s3, s2, s1, s0, startState, hw4, h4KW, hprodPtrW])
      (by simp [hprodPtrW, h3W, h2KW, h4W])
      ⟨⟨heap + K + K + 4 * K, heap + K + K + 6 * K, 2 * K, heap + K + K + 6 * K + 2 * K, rfl,
        by omega, by omega, hProdV4, hExtDV, by rw [hExtDEq]; omega⟩, hz4, h5W⟩ ω
  obtain ⟨hr5v, _, _, hFr5, hz5, hQuotV, hQuotEq⟩ := hp5
  change r5v = heap + K + K + 6 * K + 2 * K + Num.integerDivideSpace (2 * K) at hr5v
  rw [h5Eq] at hr5v; subst hr5v
  change ∀ a < heap + K + K + 6 * K + 2 * K, s10.mem a = s9.mem a at hFr5
  change ZeroFrom s10.mem nextHeap at hz5
  set qPtr := heap + K + K + 6 * K + 2 * K + 2 * (2 * K) + Num.unsignedDivideSpace (2 * K)
  have hqPtrEq : nextHeap - 2 * K = qPtr := by
    dsimp only [nextHeap, wireCoreLenEdgeSpace, qPtr]; rw [hIntDivSp]; omega
  change Num.Valid s10.mem qPtr 4 (2 * K) at hQuotV
  change Num.intVal s10.mem qPtr 4 (2 * K) =
    Num.wrap 4 (2 * K) (Num.floorDiv
      (Num.intVal s9.mem (heap + K + K + 4 * K) 4 (2 * K))
      (Num.intVal s9.mem (heap + K + K + 6 * K) 4 (2 * K))) at hQuotEq
  rw [hProdEq4, hExtDEq, hFdiv] at hQuotEq
  -- Call 6: `copy [nextHeap - 2 * K, outPtr + e * L, L]`
  have hqPtrW : qPtr < 2 ^ w := by omega
  have hnextW : nextHeap < 2 ^ w := by omega
  obtain ⟨s11, c6, _, rc6, hp6, _, hs11Regs, hc6⟩ :=
    runs_call_of_meetsContract (r := 18)
      (args := [.bin .sub (.reg 17) (.reg 9), .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5])
      hCopy (st := s10) (vs := [qPtr, outPtr + e * L, L])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hr10_17, hs10Regs 9 (by decide),
        hs10Regs 3 (by decide), hs10Regs 4 (by decide), hs10Regs 5 (by decide),
        hs9Regs 9 (by decide), hs9Regs 3 (by decide), hs9Regs 4 (by decide), hs9Regs 5 (by decide),
        hs8Regs 9 (by decide), hs8Regs 3 (by decide), hs8Regs 4 (by decide), hs8Regs 5 (by decide),
        hs7Regs 9 (by decide), hs7Regs 3 (by decide), hs7Regs 4 (by decide), hs7Regs 5 (by decide),
        hs6Regs 9 (by decide), hs6Regs 3 (by decide), hs6Regs 4 (by decide), hs6Regs 5 (by decide),
        s5, s4, s3, s2, s1, s0, startState, hqPtrEq, hqPtrW, heLW, houtA])
      (by simp [hqPtrW, houtA, hLW])
      ⟨qPtr, outPtr + e * L, L, rfl, by omega, by omega, by omega, Or.inl (by omega)⟩ ω
  obtain ⟨_, _, _, haC6, _, hCp6, hFr6⟩ := hp6
  simp only [List.cons.injEq, and_true] at haC6; obtain ⟨rfl, rfl, rfl⟩ := haC6
  -- Return `nextHeap` from reg 17
  have rRet : Runs w p ω (.ret (.reg 17)) s11 (.returned nextHeap) s11 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, hs11Regs 17 (by decide), hr10_17], rfl, rfl, rfl⟩
  have rAll : Runs w p ω (wireCoreLenEdgeBody signExt mul intDiv copy) s0 (.returned nextHeap) s11
      (6 + (4 + (6 + (6 + (6 + (c1 + (c2 + (c3 + (c4 + (c5 + (c6 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 6, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 6, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 6, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 6, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, c1, _, rc1,
    runs_seq_iff.mpr (Or.inr ⟨s7, c2, _, rc2,
    runs_seq_iff.mpr (Or.inr ⟨s8, c3, _, rc3,
    runs_seq_iff.mpr (Or.inr ⟨s9, c4, _, rc4,
    runs_seq_iff.mpr (Or.inr ⟨s10, c5, _, rc5,
    runs_seq_iff.mpr (Or.inr ⟨s11, c6, 2, rc6, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Verify output validity, exact fixed-point value, `ZeroFrom`, frame, and cost bound
  have hOutV : Num.Valid s11.mem (outPtr + e * L) 4 L := fun i hi => by
    rw [hCp6 i hi]; exact hQuotV i (by omega)
  have hOutInt : Num.intVal s11.mem (outPtr + e * L) 4 L = q := by
    rw [Num.intVal_congr hCp6, Num.intVal_prefix_wrap hQuotV (by omega), hQuotEq,
      Num.wrap_prefix_wrap (by omega), Num.wrap_of_fits hqFits]
  have hOutFix : Num.fixVal s11.mem (outPtr + e * L) 4 L P = coreLen forest ℓ e := by
    unfold Num.fixVal; rw [hOutInt]; exact hqVal
  have hzEnd : ZeroFrom s11.mem nextHeap := fun a ha =>
    (hFr6 a (Or.inr (by omega))).trans (hz5 a ha)
  have hFrameEnd : ∀ a < heap, (a < outPtr + e * L ∨ outPtr + e * L + L ≤ a) → s11.mem a = mem a :=
    fun a ha hsep =>
      (hFr6 a hsep).trans ((hFr5 a (by omega)).trans ((hFr4 a (by omega)).trans
        ((hFr3 a (by omega)).trans ((hFr2 a (by omega)).trans (hFr1 a ha)))))
  -- Bound the 6 call costs
  have hc1' : c1 ≤ 30 * K + 47 := by
    have hsz : argsSize [.reg 10, .reg 6, .reg 8, .reg 7] = 4 := rfl
    have hcs : (Num.signExtendContract w 4).cost [numPtr + e * Lw, Lw, K, heap] s5.mem = 30 * K + 42 := rfl
    rw [hsz, hcs] at hc1; exact Nat.le_trans hc1 (by omega)
  have hc2' : c2 ≤ 30 * K + 47 := by
    have hsz : argsSize [.reg 11, .reg 5, .reg 8, .reg 13] = 4 := rfl
    have hcs : (Num.signExtendContract w 4).cost [lenPtr + e * L, L, K, heap + K] s6.mem = 30 * K + 42 := rfl
    rw [hsz, hcs] at hc2; exact Nat.le_trans hc2 (by omega)
  have hc3' : c3 ≤ 152 * K ^ 2 + 190 * K + 104 := by
    have hsz : argsSize [.reg 7, .reg 13, .reg 8, .reg 14] = 4 := rfl
    have hcs : (Num.multiplyContract w 4).cost [heap, heap + K, K, heap + K + K] s7.mem =
        (2 * K) * (38 * (2 * K) + 35) + 120 * K + 99 := rfl
    rw [hsz, hcs] at hc3
    have hring : (2 * K) * (38 * (2 * K) + 35) + 120 * K + 99 = 152 * K ^ 2 + 190 * K + 99 := by ring
    rw [hring] at hc3
    exact hc3.trans (Nat.le_of_eq (by ring))
  have hc4' : c4 ≤ 60 * K + 47 := by
    have hsz : argsSize [.reg 12, .reg 6, .reg 9, .reg 15] = 4 := rfl
    have hcs : (Num.signExtendContract w 4).cost [denPtr + e * Lw, Lw, 2 * K, heap + K + K + 6 * K] s8.mem =
        30 * (2 * K) + 42 := rfl
    rw [hsz, hcs] at hc4; omega
  have hc5' : c5 ≤ 1200 * K ^ 2 + 1648 * K + 409 := by
    have hsz : argsSize [.bin .add (.reg 14) (.bin .mul (.const 4) (.reg 8)), .reg 15, .reg 9, .reg 16] = 8 := rfl
    have hcs : (Num.integerDivideContract w 4).cost
        [heap + K + K + 4 * K, heap + K + K + 6 * K, 2 * K, heap + K + K + 6 * K + 2 * K] s9.mem =
        (2 * K) * (300 * (2 * K) + 644) + 180 * (2 * K) + 400 := rfl
    rw [hsz, hcs] at hc5
    have hring : (2 * K) * (300 * (2 * K) + 644) + 180 * (2 * K) + 400 =
        1200 * K ^ 2 + 1648 * K + 400 := by ring
    rw [hring] at hc5
    exact hc5.trans (Nat.le_of_eq (by ring))
  have hc6' : c6 ≤ 17 * K + 20 := by
    have hsz : argsSize [.bin .sub (.reg 17) (.reg 9), .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5] = 9 := rfl
    have hcs : (copyWordsContract w).cost [qPtr, outPtr + e * L, L] s10.mem = 17 * L + 10 := rfl
    rw [hsz, hcs] at hc6; omega
  refine ⟨s11, _, rAll, ?_, hOutV, hOutFix, hzEnd, hFrameEnd⟩
  unfold wireCoreLenEdgeCost
  set K2 := K ^ 2
  omega

/-! ### Full `coreLen` table builder theorem -/

/-- Execution theorem for `wireCoreLenBody`: writes `EdgeValuesAt out.mem heap 4 L P H.E (coreLen forest ℓ)`
for any `L_w`-limb `StretchValuesAt` readout of `forest` and `L`-limb `EdgeValuesAt` of `ℓ`. -/
theorem wireCoreLen_runs
    {w L Lw P hBase vcH ecH stretchDesc lenPtr heap edgeProc : ℕ}
    {H : MGraph} {G_E : Finset ℕ} {forest : LSF} {ℓ : ℕ → ℝ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    {signExt mul intDiv copy : ℕ}
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hH : DynGraphAt mem hBase vcH ecH H)
    (hSub : H.E ⊆ G_E)
    (hSt : StretchValuesAt mem stretchDesc 4 Lw P G_E forest.wstr)
    (hLen : EdgeValuesAt mem lenPtr 4 L P G_E ℓ)
    (hFits : ∀ e ∈ H.E, ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = coreLen forest ℓ e)
    (hHLe : hBase + dynGraphSize vcH ecH ≤ heap)
    (hStLe : stretchDesc + 2 ≤ heap)
    (hNumLe : ∀ e ∈ H.E, mem stretchDesc + e * Lw + Lw ≤ heap)
    (hDenLe : ∀ e ∈ H.E, mem (stretchDesc + 1) + e * Lw + Lw ≤ heap)
    (hLenLe : ∀ e ∈ H.E, lenPtr + e * L + L ≤ heap)
    (hz : ZeroFrom mem heap)
    (hRoom : heap + ecH * L + H.m * wireCoreLenEdgeSpace (max L Lw) < 2 ^ w)
    (hw7 : 7 < 2 ^ w) :
    let K := max L Lw
    let nextHeap := heap + ecH * L + H.m * wireCoreLenEdgeSpace K
    ∃ out cost, Runs w p ω (wireCoreLenBody edgeProc)
        (startState [hBase, stretchDesc, lenPtr, L, Lw, heap] mem pos)
        (.returned nextHeap) out cost ∧
      cost ≤ H.m * (wireCoreLenEdgeCost K + 30) + 60 ∧
      EdgeValuesAt out.mem heap 4 L P H.E (coreLen forest ℓ) ∧
      ZeroFrom out.mem nextHeap ∧
      ∀ a < heap, out.mem a = mem a := by
  intro K nextHeap
  change heap + ecH * L + H.m * wireCoreLenEdgeSpace K < 2 ^ w at hRoom
  obtain ⟨eL, heLLen, heLNodup, heLMem, heLAt, _⟩ := hH.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvcH : mem hBase = vcH := by simpa [dgVCapOff] using hH.2.2.2.1
  have hecH : mem (hBase + 1) = ecH := by simpa [dgECapOff] using hH.2.2.2.2.1
  have hmH : mem (hBase + 3) = H.m := by simpa [dgMOff] using hH.2.2.2.2.2.2.1
  set numPtr := mem stretchDesc
  set denPtr := mem (stretchDesc + 1)
  set eList := dgEListBase hBase vcH ecH
  -- Setup registers 6..12
  let s0 := startState [hBase, stretchDesc, lenPtr, L, Lw, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 6 vcH }
  let s2 := { s1 with regs := Function.update s1.regs 7 ecH }
  let s3 := { s2 with regs := Function.update s2.regs 8 H.m }
  let s4 := { s3 with regs := Function.update s3.regs 9 eList }
  let s5 := { s4 with regs := Function.update s4.regs 10 numPtr }
  let s6 := { s5 with regs := Function.update s5.regs 11 denPtr }
  let s7 := { s6 with regs := Function.update s6.regs 12 (heap + ecH * L) }
  have h7vc : 7 * vcH < 2 ^ w := by unfold dynGraphSize at hHLe; omega
  have hbh4 : hBase + 4 < 2 ^ w := by unfold dynGraphSize at hHLe; omega
  have hbh7 : hBase + 4 + 7 * vcH < 2 ^ w := by unfold dynGraphSize at hHLe; omega
  have heListW : hBase + 4 + 7 * vcH + ecH < 2 ^ w := by unfold dynGraphSize at hHLe; omega
  have r1 : Runs w p ω (.assign 6 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨vcH, by simp [Expr.eval, s0, startState, hvcH], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨ecH, by simp [Expr.eval, BinOp.eval, s1, s0, startState,
      show 1 < 2 ^ w by omega, show hBase + 1 < 2 ^ w by omega, hecH], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 3)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨H.m, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState,
      show 3 < 2 ^ w by omega, show hBase + 3 < 2 ^ w by omega, hmH], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
      (.bin .mul (.const 7) (.reg 6))) (.reg 7))) s3 .normal s4 10 :=
    runs_assign_iff.mpr ⟨eList, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState,
      show 4 < 2 ^ w by omega, hw7, h7vc, hbh4, hbh7, heListW, eList, dgEListBase], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 10 (.load (.reg 1))) s4 .normal s5 3 :=
    runs_assign_iff.mpr ⟨numPtr, by simp [Expr.eval, s4, s3, s2, s1, s0, startState, numPtr], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 1) (.const 1)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨denPtr, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState,
      show 1 < 2 ^ w by omega, show stretchDesc + 1 < 2 ^ w by omega, denPtr], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 12 (.bin .add (.reg 5) (.bin .mul (.reg 7) (.reg 3)))) s6 .normal s7 6 :=
    runs_assign_iff.mpr ⟨heap + ecH * L, by simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0,
      startState, show ecH * L < 2 ^ w by omega, show heap + ecH * L < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Loop induction over `done ++ rem = eL`
  have hLoop : ∀ (done rem : List ℕ) (st : State),
      done ++ rem = eL →
      st.regs 2 = lenPtr → st.regs 3 = L → st.regs 4 = Lw → st.regs 5 = heap →
      st.regs 8 = rem.length → st.regs 9 = eList + done.length →
      st.regs 10 = numPtr → st.regs 11 = denPtr →
      st.regs 12 = heap + ecH * L + done.length * wireCoreLenEdgeSpace K →
      (∀ e ∈ done, Num.Valid st.mem (heap + e * L) 4 L ∧
        Num.fixVal st.mem (heap + e * L) 4 L P = coreLen forest ℓ e) →
      ZeroFrom st.mem (heap + ecH * L + done.length * wireCoreLenEdgeSpace K) →
      (∀ a < heap, st.mem a = mem a) →
      ∃ out c, Runs w p ω
          (.loop (.reg 8)
            (.assign 13 (.load (.reg 9)) ;;
             .call 12 edgeProc [.reg 10, .reg 11, .reg 2, .reg 5, .reg 13, .reg 3, .reg 4, .reg 12] ;;
             .assign 9 (.bin .add (.reg 9) (.const 1)) ;;
             .assign 8 (.bin .sub (.reg 8) (.const 1))))
          st .normal out c ∧
        c ≤ rem.length * (wireCoreLenEdgeCost K + 30) + 2 ∧
        out.regs 12 = nextHeap ∧
        (∀ e ∈ eL, Num.Valid out.mem (heap + e * L) 4 L ∧
          Num.fixVal out.mem (heap + e * L) 4 L P = coreLen forest ℓ e) ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, out.mem a = mem a) := by
    intro done rem
    induction rem generalizing done with
    | nil =>
      intro st happ _ _ _ _ hr8 _ _ _ hr12 hdone hzCur hfr
      have hdEq : done = eL := by simpa using happ
      subst hdEq
      have h12End : st.regs 12 = nextHeap := by rw [hr12, heLLen]
      exact ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr8], rfl, rfl, rfl⟩),
        by omega, h12End, hdone, by rwa [heLLen] at hzCur, hfr⟩
    | cons e rest ih =>
      intro st happ hr2 hr3 hr4 hr5 hr8 hr9 hr10 hr11 hr12 hdone hzCur hfr
      have heMem : e ∈ H.E := (heLMem e).mp (by rw [← happ]; simp)
      have heG : e ∈ G_E := hSub heMem
      have heLtEc : e < ecH := hH.2.2.1 e heMem
      have hLenEq : done.length + rest.length + 1 = H.m := by
        have := congrArg List.length happ; simp only [List.length_append, List.length_cons] at this; omega
      have heAtList : st.mem (eList + done.length) = e := by
        have hlt : done.length < eL.length := by omega
        have h1 : mem (eList + done.length) = eL[done.length] := heLAt done.length hlt
        have h2 : eL[done.length] = e := by
          have : (done ++ e :: rest)[done.length]'(by simp) = e := by simp
          simpa [happ] using this
        have hltH : eList + done.length < heap := by
          unfold eList dgEListBase; unfold dynGraphSize at hHLe
          have hmLe : H.m ≤ ecH := by
            have hsub : H.E ⊆ Finset.range ecH := fun x hx => Finset.mem_range.mpr (hH.2.2.1 x hx)
            simpa [MGraph.m] using Finset.card_le_card hsub
          omega
        exact (hfr _ hltH).trans (h1.trans h2)
      let curH := heap + ecH * L + done.length * wireCoreLenEdgeSpace K
      have hcurHW : curH < 2 ^ w := by
        have : done.length * wireCoreLenEdgeSpace K ≤ H.m * wireCoreLenEdgeSpace K :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      let t1 := { st with regs := Function.update st.regs 13 e }
      have rt1 : Runs w p ω (.assign 13 (.load (.reg 9))) st .normal t1 3 :=
        runs_assign_iff.mpr ⟨e, by simp [Expr.eval, hr9, heAtList], rfl, rfl, rfl⟩
      obtain ⟨q, hqFits, hqVal⟩ := hFits e heMem
      have hNumV : Num.Valid st.mem (numPtr + e * Lw) 4 Lw := fun i hi => by
        rw [hfr _ (by have := hNumLe e heMem; omega)]; exact (hSt e heG).1 i hi
      have hDenV : Num.Valid st.mem (denPtr + e * Lw) 4 Lw := fun i hi => by
        rw [hfr _ (by have := hDenLe e heMem; omega)]; exact (hSt e heG).2.1 i hi
      have hLenV : Num.Valid st.mem (lenPtr + e * L) 4 L := fun i hi => by
        rw [hfr _ (by have := hLenLe e heMem; omega)]; exact (hLen e heG).1 i hi
      have hNumFix : Num.fixVal st.mem (numPtr + e * Lw) 4 Lw P =
          Num.fixVal mem (numPtr + e * Lw) 4 Lw P := by
        unfold Num.fixVal; rw [Num.intVal_congr (fun i hi => hfr _ (by have := hNumLe e heMem; omega))]
      have hDenFix : Num.fixVal st.mem (denPtr + e * Lw) 4 Lw P =
          Num.fixVal mem (denPtr + e * Lw) 4 Lw P := by
        unfold Num.fixVal; rw [Num.intVal_congr (fun i hi => hfr _ (by have := hDenLe e heMem; omega))]
      have hLenFix : Num.fixVal st.mem (lenPtr + e * L) 4 L P = ℓ e := by
        unfold Num.fixVal; rw [Num.intVal_congr (fun i hi => hfr _ (by have := hLenLe e heMem; omega))]
        exact (hLen e heG).2
      have houtLe : heap + e * L + L ≤ curH := by
        have : (e + 1) * L ≤ ecH * L := Nat.mul_le_mul_right L (by omega)
        have : e * L + L = (e + 1) * L := by ring
        omega
      have hStepRoom : curH + wireCoreLenEdgeSpace K < 2 ^ w := by
        have h1 : (done.length + 1) * wireCoreLenEdgeSpace K ≤ H.m * wireCoreLenEdgeSpace K :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (done.length + 1) * wireCoreLenEdgeSpace K =
            done.length * wireCoreLenEdgeSpace K + wireCoreLenEdgeSpace K := by ring
        omega
      obtain ⟨outE, cE, rE, hcE, hEV, hEFix, hzE, hFrE⟩ :=
        wireCoreLenEdge_runs hSign hMul hDiv hCopy hNumV hDenV hLenV
          (hDenFix.symm ▸ (hSt e heG).2.2.1)
          (by rw [hNumFix, hDenFix]; exact (hSt e heG).2.2.2)
          hLenFix hqFits hqVal
          (by have := hNumLe e heMem; omega) (by have := hDenLe e heMem; omega)
          (by have := hLenLe e heMem; omega) houtLe hzCur hStepRoom (by omega)
      let t2 : State :=
        { regs := Function.update t1.regs 12 (curH + wireCoreLenEdgeSpace K)
          mem := outE.mem
          pos := outE.pos }
      have rt2 : Runs w p ω
          (.call 12 edgeProc [.reg 10, .reg 11, .reg 2, .reg 5, .reg 13, .reg 3, .reg 4, .reg 12])
          t1 .normal t2 (cE + 9) :=
        runs_call_iff.mpr ⟨[numPtr, denPtr, lenPtr, heap, e, L, Lw, curH],
          wireCoreLenEdgeBody signExt mul intDiv copy, .returned (curH + wireCoreLenEdgeSpace K), outE, cE,
          by simp [evalArgs, Expr.eval, t1, hr10, hr11, hr2, hr5, hr3, hr4, hr12, curH],
          hEdgeProc, rE, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      let t3 := { t2 with regs := Function.update t2.regs 9 (eList + done.length + 1) }
      let t4 := { t3 with regs := Function.update t3.regs 8 rest.length }
      have hmLe : H.m ≤ ecH := by
        have hsub : H.E ⊆ Finset.range ecH := fun x hx => Finset.mem_range.mpr (hH.2.2.1 x hx)
        simpa [MGraph.m] using Finset.card_le_card hsub
      have hlist1W : eList + done.length + 1 < 2 ^ w := by
        unfold eList dgEListBase; unfold dynGraphSize at hHLe; omega
      have hrestW : rest.length < 2 ^ w := by unfold dynGraphSize at hHLe; omega
      have rt3 : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) t2 .normal t3 4 :=
        runs_assign_iff.mpr ⟨eList + done.length + 1, by simp [Expr.eval, BinOp.eval, t2, t1, hr9,
          show 1 < 2 ^ w by omega, hlist1W], rfl, rfl, rfl⟩
      have rt4 : Runs w p ω (.assign 8 (.bin .sub (.reg 8) (.const 1))) t3 .normal t4 4 :=
        runs_assign_iff.mpr ⟨rest.length, by simp [Expr.eval, BinOp.eval, t3, t2, t1, hr8,
          show 1 < 2 ^ w by omega, hrestW], rfl, rfl, rfl⟩
      have rBody : Runs w p ω _ st .normal t4 (3 + ((cE + 9) + (4 + 4 + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1,
        runs_seq_iff.mpr (Or.inr ⟨t2, cE + 9, _, rt2,
        runs_seq_iff.mpr (Or.inr ⟨t3, 4, 4, rt3, rt4, rfl⟩), rfl⟩), rfl⟩)
      have hdone' : ∀ f ∈ done ++ [e], Num.Valid t4.mem (heap + f * L) 4 L ∧
          Num.fixVal t4.mem (heap + f * L) 4 L P = coreLen forest ℓ f := by
        intro f hf
        rcases List.mem_append.mp hf with hfD | hfE
        · have hne : f ≠ e := by
            have hnd := happ ▸ heLNodup
            intro heq; subst heq
            exact (List.nodup_append.mp hnd).2.2 f hfD f List.mem_cons_self rfl
          have hfMem : f ∈ H.E := (heLMem f).mp (by rw [← happ]; exact List.mem_append_left _ hfD)
          have hfEc : f < ecH := hH.2.2.1 f hfMem
          have hsep : ∀ i < L, heap + f * L + i < heap + e * L ∨ heap + e * L + L ≤ heap + f * L + i := by
            intro i hi
            by_cases hlt : f < e
            · left
              have h1 : (f + 1) * L ≤ e * L := Nat.mul_le_mul_right L (by omega)
              have h2 : f * L + L = (f + 1) * L := by ring
              omega
            · right
              have h1 : (e + 1) * L ≤ f * L := Nat.mul_le_mul_right L (by omega)
              have h2 : e * L + L = (e + 1) * L := by ring
              omega
          have hltCur : ∀ i < L, heap + f * L + i < curH := fun i hi => by
            have h1 : (f + 1) * L ≤ ecH * L := Nat.mul_le_mul_right L (by omega)
            have h2 : f * L + L = (f + 1) * L := by ring
            omega
          have hEqI : ∀ i < L, t4.mem (heap + f * L + i) = st.mem (heap + f * L + i) :=
            fun i hi => hFrE _ (hltCur i hi) (hsep i hi)
          refine ⟨fun i hi => (hEqI i hi).symm ▸ (hdone f hfD).1 i hi, ?_⟩
          unfold Num.fixVal; rw [Num.intVal_congr hEqI]; exact (hdone f hfD).2
        · cases List.mem_singleton.mp hfE; exact ⟨hEV, hEFix⟩
      have hCurNext : curH + wireCoreLenEdgeSpace K =
          heap + ecH * L + (done ++ [e]).length * wireCoreLenEdgeSpace K := by
        simp only [curH, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]; omega
      obtain ⟨out, cRest, rRest, hcRest, hout12, houtDone, hzRest, hfrRest⟩ :=
        ih (done ++ [e]) t4 (by simpa [List.append_assoc] using happ)
          (by simp [t4, t3, t2, t1, hr2]) (by simp [t4, t3, t2, t1, hr3])
          (by simp [t4, t3, t2, t1, hr4]) (by simp [t4, t3, t2, t1, hr5])
          (by simp [t4]) (by simp [t4, t3, List.length_append]; omega)
          (by simp [t4, t3, t2, t1, hr10]) (by simp [t4, t3, t2, t1, hr11])
          (by simp [t4, t3, t2, hCurNext]) hdone' (hCurNext ▸ hzE)
          (fun a ha => (hFrE a (by omega) (Or.inl (by omega))).trans (hfr a ha))
      refine ⟨out, (3 + ((cE + 9) + (4 + 4 + 1) + 1) + 1) + cRest + 2,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨rest.length + 1, t4, _, cRest,
          by simp [Expr.eval, hr8], Nat.succ_ne_zero _, rBody, rRest, by simp [Expr.size]; omega⟩)),
        ?_, hout12, houtDone, hzRest, hfrRest⟩
      change cE ≤ wireCoreLenEdgeCost K at hcE
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  obtain ⟨out, cLoop, rLoop, hcLoop, hout12, houtE, hzOut, hfrOut⟩ :=
    hLoop [] eL s7 rfl (by simp [s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s7, s6, s5, s4, s3, heLLen]) (by simp [s7, s6, s5, s4])
      (by simp [s7, s6, s5]) (by simp [s7, s6]) (by simp [s7])
      (fun _ h => by cases h) (fun a ha => hz a (by omega)) (fun _ _ => rfl)
  have rRet : Runs w p ω (.ret (.reg 12)) out (.returned nextHeap) out 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, hout12], rfl, rfl, rfl⟩
  have rAll : Runs w p ω (wireCoreLenBody edgeProc) s0 (.returned nextHeap) out
      (3 + (5 + (5 + (10 + (3 + (5 + (6 + (cLoop + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 10, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 3, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 6, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨out, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨out, _, rAll, ?_, fun e he => houtE e ((heLMem e).mpr he), hzOut, hfrOut⟩
  rw [heLLen] at hcLoop
  omega

end MinCostFlow.MinRatio
