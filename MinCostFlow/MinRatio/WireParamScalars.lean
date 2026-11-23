module

public import MinCostFlow.MinRatio.WireParamMath
public import MinCostFlow.Num.IPM.BitLength
public import MinCostFlow.Scaling.ClogTwoProgram
import Mathlib.Tactic

/-!
# Deterministic scalar parameter subroutine for parameter setup

Provides `computeScalarParamsStmt bitLen clog threshold A`: given `reg 0 = m`, `reg 1 = V`,
`reg 4 = heap`, computes `M₀ = max m threshold`, `N₀ = 4 * M₀`,
`quality = cappedQualityExponent threshold A m`, `epsExp = quality + alphaExponent m V + 10`,
`psi = paramPsi threshold A m V`, and the initial scratch cursor
`reg 98 = heap + 6 + (M₀ + 2).size` in registers, preserving memory and `reg 0`, in
`O(m.size + V.size + M₀.size)` steps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine Final

/-! ## Part 1: Scalar parameters in registers -/

/-- Compute `[M₀, N₀, quality, epsExp, psi]` and the scratch cursor `heap + 6 + (M₀ + 2).size`
in registers `22, 86, 83, 84, 85, 98`, saving `(m, V, heap)` in `80, 81, 82` and preserving
`reg 0 = m` and memory. -/
@[expose] def computeScalarParamsStmt (bitLen clog threshold A : ℕ) : Stmt :=
  .assign 80 (.reg 0) ;;
  .assign 81 (.reg 1) ;;
  .assign 82 (.reg 4) ;;
  .cond (.bin .lt (.reg 80) (.const threshold))
    (.assign 22 (.const threshold))
    (.assign 22 (.reg 80)) ;;
  .assign 86 (.bin .mul (.const 4) (.reg 22)) ;;
  .call 5 bitLen [.reg 80] ;;
  .call 6 bitLen [.reg 81] ;;
  .call 7 bitLen [.reg 22] ;;
  .call 8 bitLen [.bin .add (.reg 22) (.const 2)] ;;
  .call 9 bitLen [.bin .add (.reg 7) (.const 1)] ;;
  .assign 98 (.bin .add (.bin .add (.reg 82) (.const 6)) (.reg 8)) ;;
  .assign 10 (.bin .div (.bin .add (.bin .mul (.const 47) (.reg 9)) (.const 47)) (.const 48)) ;;
  .assign 11 (.bin .shiftLeft (.const 1) (.reg 10)) ;;
  .assign 83 (.bin .mul (.bin .mul (.const (128 * (A + 1))) (.reg 9)) (.reg 11)) ;;
  .call 12 clog [.bin .mul (.const 1000) (.bin .add (.reg 5) (.reg 6))] ;;
  .assign 84 (.bin .add (.bin .add (.reg 83) (.reg 12)) (.const 10)) ;;
  .assign 13 (.bin .mul (.const 220000)
    (.bin .mul (.bin .add (.reg 5) (.reg 6)) (.bin .add (.reg 5) (.reg 6)))) ;;
  .cond (.bin .lt (.reg 13) (.reg 83))
    (.assign 14 (.reg 83))
    (.assign 14 (.reg 13)) ;;
  .assign 15 (.bin .add (.bin .add (.reg 5) (.reg 6)) (.const 5)) ;;
  .assign 16 (.bin .add (.bin .add (.bin .mul (.const 4) (.reg 14))
    (.bin .mul (.const 2) (.reg 15))) (.const 100)) ;;
  .assign 85 (.bin .add (.bin .add (.reg 16) (.reg 13)) (.const 6))

theorem computeScalarParamsStmt_noRand (bitLen clog threshold A : ℕ) :
    (computeScalarParamsStmt bitLen clog threshold A).NoRand := by
  simp [computeScalarParamsStmt, Stmt.NoRand]

/-- Step-cost bound for `computeScalarParamsStmt`. -/
@[expose] def scalarParamsCost (m V M₀ : ℕ) : ℕ :=
  14 * (m.size + V.size + M₀.size + (M₀ + 2).size + (M₀.size + 1).size) +
    40 * Num.IPM.alphaExponent m V + 400

theorem computeScalarParamsStmt_runs
    {w bitLen clog threshold A m V heap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bitLen Num.IPM.bitLengthContract)
    (hclog : MeetsContract w p clog
      (Scaling.Machine.clogTwoContract w (Num.IPM.alphaScale m V)))
    (h0 : st.regs 0 = m) (h1 : st.regs 1 = V) (h4 : st.regs 4 = heap)
    (hmW : m < 2 ^ w) (hVW : V < 2 ^ w) (hthrW : threshold < 2 ^ w)
    (hM0_2W : max m threshold + 2 < 2 ^ w)
    (hN0W : 4 * max m threshold < 2 ^ w)
    (hqualW : paramQuality threshold A m < 2 ^ w)
    (halphaScaleW : Num.IPM.alphaScale m V + 1 < 2 ^ w)
    (hepsW : paramEpsExp threshold A m V < 2 ^ w)
    (hpsiW : paramPsi threshold A m V < 2 ^ w)
    (hscrW : heap + 6 + (max m threshold + 2).size < 2 ^ w)
    (h220000W : 220000 < 2 ^ w) :
    let M₀ := paramM0 threshold m
    ∃ out c, Runs w p ω (computeScalarParamsStmt bitLen clog threshold A) st .normal out c ∧
      out.regs 0 = m ∧ out.regs 22 = M₀ ∧
      out.regs 80 = m ∧ out.regs 81 = V ∧ out.regs 82 = heap ∧
      out.regs 83 = paramQuality threshold A m ∧
      out.regs 84 = paramEpsExp threshold A m V ∧
      out.regs 85 = paramPsi threshold A m V ∧
      out.regs 86 = paramN0 threshold m ∧
      out.regs 98 = heap + 6 + (M₀ + 2).size ∧
      out.mem = st.mem ∧ c ≤ scalarParamsCost m V M₀ := by
  intro M₀
  have hM0_eq : M₀ = max m threshold := rfl
  have hM0W : M₀ < 2 ^ w := by omega
  have hb_pos : 0 < (M₀.size + 1).size := Nat.size_pos.mpr (by omega)
  let b := (M₀.size + 1).size
  let sh := (47 * b + 47) / 48
  let q := paramQuality threshold A m
  have hq_eq : q = 128 * (A + 1) * b * 2 ^ sh := by
    simp [q, paramQuality, cappedQualityExponent, chainEdgeCap, integerQualityExponent, b, sh, M₀, paramM0]
  have hpow_pos : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
  have h128bW : 128 * (A + 1) * b < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hpow_pos) (hq_eq ▸ hqualW)
  have h128W : 128 * (A + 1) < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hb_pos) h128bW
  have h47b47W : 47 * b + 47 < 2 ^ w := by
    have h1 : 128 * b ≤ 128 * (A + 1) * b :=
      Nat.mul_le_mul_right b (Nat.le_mul_of_pos_right 128 (Nat.succ_pos A))
    omega
  have hshW : sh < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) h47b47W
  have h2shW : 2 ^ sh < 2 ^ w := by
    have h1 : 1 ≤ 128 * (A + 1) * b := Nat.mul_pos (by omega) hb_pos
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ h1) (hq_eq ▸ hqualW)
  have hmszW : m.size < 2 ^ w := (Nat.size_le.mpr hmW).trans_lt (Nat.lt_pow_self (by decide))
  have hVszW : V.size < 2 ^ w := (Nat.size_le.mpr hVW).trans_lt (Nat.lt_pow_self (by decide))
  have hw18 : 18 ≤ w := by
    by_contra hlt
    have h1 : 2 ^ w ≤ 2 ^ 17 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 17 = 131072 := by decide
    omega
  have hM0sz1W : M₀.size + 1 < 2 ^ w := by
    have h1 : M₀.size ≤ w := Nat.size_le.mpr hM0W
    have h2 : w + 1 < 2 ^ w := by
      have := Nat.lt_two_pow_self (n := w - 1)
      have h3 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      have h4 : 2 ^ 1 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega
  have hN0W' : 4 * M₀ < 2 ^ w := hN0W
  have hM0_2W' : M₀ + 2 < 2 ^ w := hM0_2W
  have hscrW' : heap + 6 + (M₀ + 2).size < 2 ^ w := hscrW
  -- Stage 1: save registers 80, 81, 82 and compute M₀ in reg 22, N₀ in reg 86
  let s1 := { st with regs := Function.update st.regs 80 m }
  let s2 := { s1 with regs := Function.update s1.regs 81 V }
  let s3 := { s2 with regs := Function.update s2.regs 82 heap }
  let s4 := { s3 with regs := Function.update s3.regs 22 M₀ }
  let s5 := { s4 with regs := Function.update s4.regs 86 (4 * M₀) }
  have r1 : Runs w p ω (.assign 80 (.reg 0)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨m, by simp [Expr.eval, h0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 81 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨V, by simp [Expr.eval, s1, h1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 82 (.reg 4)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s2, s1, h4], rfl, rfl, rfl⟩
  have r4 : Runs w p ω
      (.cond (.bin .lt (.reg 80) (.const threshold)) (.assign 22 (.const threshold)) (.assign 22 (.reg 80)))
      s3 .normal s4 6 := by
    by_cases hlt : m < threshold
    · have hM0 : M₀ = threshold := max_eq_right hlt.le
      refine runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hthrW, hlt, show 1 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨threshold, by simp [Expr.eval, hthrW], rfl, by simp [s4, hM0], rfl⟩, rfl⟩
    · have hM0 : M₀ = m := max_eq_left (by omega)
      refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hthrW, hlt, show 0 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨m, by simp [Expr.eval, s3, s2, s1], rfl, by simp [s4, hM0], rfl⟩, rfl⟩
  have r5 : Runs w p ω (.assign 86 (.bin .mul (.const 4) (.reg 22))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨4 * M₀, by simp [Expr.eval, BinOp.eval, s4, show 4 < 2 ^ w by omega, hN0W'],
      rfl, rfl, rfl⟩
  -- Stage 2: five bitLength calls
  have ha6 : evalArgs w s5 [.reg 80] = some [m] := by simp [evalArgs, Expr.eval, s5, s4, s3, s2, s1]
  obtain ⟨s6, c6, v6, r6, hp6, hs6_5, hs6_keep, hc6⟩ :=
    runs_call_of_meetsContract (r := 5) hbits ha6 (by simpa using hmW) ⟨m, rfl⟩ ω
  obtain ⟨hm6, rfl⟩ := hp6
  have hs6_81 : s6.regs 81 = V := (hs6_keep 81 (by decide)).trans (by simp [s5, s4, s3, s2])
  have ha7 : evalArgs w s6 [.reg 81] = some [V] := by simp [evalArgs, Expr.eval, hs6_81]
  obtain ⟨s7, c7, v7, r7, hp7, hs7_6, hs7_keep, hc7⟩ :=
    runs_call_of_meetsContract (r := 6) hbits ha7 (by simpa using hVW) ⟨V, rfl⟩ ω
  obtain ⟨hm7, rfl⟩ := hp7
  have hs7_22 : s7.regs 22 = M₀ :=
    (hs7_keep 22 (by decide)).trans ((hs6_keep 22 (by decide)).trans (by simp [s5, s4]))
  have ha8 : evalArgs w s7 [.reg 22] = some [M₀] := by simp [evalArgs, Expr.eval, hs7_22]
  obtain ⟨s8, c8, v8, r8, hp8, hs8_7, hs8_keep, hc8⟩ :=
    runs_call_of_meetsContract (r := 7) hbits ha8 (by simpa using hM0W) ⟨M₀, rfl⟩ ω
  obtain ⟨hm8, rfl⟩ := hp8
  have hs8_22 : s8.regs 22 = M₀ := (hs8_keep 22 (by decide)).trans hs7_22
  have ha9 : evalArgs w s8 [.bin .add (.reg 22) (.const 2)] = some [M₀ + 2] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hs8_22, show 2 < 2 ^ w by omega, hM0_2W']
  obtain ⟨s9, c9, v9, r9, hp9, hs9_8, hs9_keep, hc9⟩ :=
    runs_call_of_meetsContract (r := 8) hbits ha9 (by simpa using hM0_2W') ⟨M₀ + 2, rfl⟩ ω
  obtain ⟨hm9, rfl⟩ := hp9
  have hs9_7 : s9.regs 7 = M₀.size := (hs9_keep 7 (by decide)).trans hs8_7
  have ha10 : evalArgs w s9 [.bin .add (.reg 7) (.const 1)] = some [M₀.size + 1] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hs9_7, show 1 < 2 ^ w by omega, hM0sz1W]
  obtain ⟨s10, c10, v10, r10, hp10, hs10_9, hs10_keep, hc10⟩ :=
    runs_call_of_meetsContract (r := 9) hbits ha10 (by simpa using hM0sz1W) ⟨M₀.size + 1, rfl⟩ ω
  obtain ⟨hm10, rfl⟩ := hp10
  have hkeep10 (r : ℕ) (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) :
      s10.regs r = s5.regs r :=
    (hs10_keep r h9).trans ((hs9_keep r h8).trans ((hs8_keep r h7).trans
      ((hs7_keep r h6).trans (hs6_keep r h5))))
  have hs10_5 : s10.regs 5 = m.size :=
    (hs10_keep 5 (by decide)).trans ((hs9_keep 5 (by decide)).trans
      ((hs8_keep 5 (by decide)).trans ((hs7_keep 5 (by decide)).trans hs6_5)))
  have hs10_6 : s10.regs 6 = V.size :=
    (hs10_keep 6 (by decide)).trans ((hs9_keep 6 (by decide)).trans
      ((hs8_keep 6 (by decide)).trans hs7_6))
  have hs10_8 : s10.regs 8 = (M₀ + 2).size := (hs10_keep 8 (by decide)).trans hs9_8
  have hs10_82 : s10.regs 82 = heap :=
    (hkeep10 82 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3])
  -- Stage 3: scratch cursor, quality, alphaExponent, epsExp, psi
  let s11 := { s10 with regs := Function.update s10.regs 98 (heap + 6 + (M₀ + 2).size) }
  let s12 := { s11 with regs := Function.update s11.regs 10 sh }
  let s13 := { s12 with regs := Function.update s12.regs 11 (2 ^ sh) }
  let s14 := { s13 with regs := Function.update s13.regs 83 q }
  have r11 : Runs w p ω (.assign 98 (.bin .add (.bin .add (.reg 82) (.const 6)) (.reg 8)))
      s10 .normal s11 6 :=
    runs_assign_iff.mpr ⟨heap + 6 + (M₀ + 2).size, by
      simp [Expr.eval, BinOp.eval, hs10_82, hs10_8, show 6 < 2 ^ w by omega,
        show heap + 6 < 2 ^ w by omega, hscrW'], rfl, rfl, rfl⟩
  have hs10_9' : s10.regs 9 = b := hs10_9
  have r12 : Runs w p ω
      (.assign 10 (.bin .div (.bin .add (.bin .mul (.const 47) (.reg 9)) (.const 47)) (.const 48)))
      s11 .normal s12 8 :=
    runs_assign_iff.mpr ⟨sh, by
      simp [Expr.eval, BinOp.eval, s11, hs10_9', sh, show 47 < 2 ^ w by omega,
        show 48 < 2 ^ w by omega, show 47 * b < 2 ^ w by omega, h47b47W, hshW], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 11 (.bin .shiftLeft (.const 1) (.reg 10))) s12 .normal s13 4 :=
    runs_assign_iff.mpr ⟨2 ^ sh, by
      simp [Expr.eval, BinOp.eval, s12, Nat.shiftLeft_eq, show 1 < 2 ^ w by omega, h2shW], rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.assign 83 (.bin .mul (.bin .mul (.const (128 * (A + 1))) (.reg 9)) (.reg 11)))
      s13 .normal s14 6 :=
    runs_assign_iff.mpr ⟨q, by
      have hmulW : 128 * (A + 1) * b * 2 ^ sh < 2 ^ w := by
        simpa [q, hq_eq] using hqualW
      simp [Expr.eval, BinOp.eval, s13, s12, s11, hs10_9', hq_eq, h128W, h128bW, hmulW], rfl, rfl, rfl⟩
  have hs14_5 : s14.regs 5 = m.size := by simp [s14, s13, s12, s11, hs10_5]
  have hs14_6 : s14.regs 6 = V.size := by simp [s14, s13, s12, s11, hs10_6]
  have hscale_eq : 1000 * (m.size + V.size) = Num.IPM.alphaScale m V := rfl
  have ha15 : evalArgs w s14 [.bin .mul (.const 1000) (.bin .add (.reg 5) (.reg 6))] =
      some [Num.IPM.alphaScale m V] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hs14_5, hs14_6, hscale_eq,
      show 1000 < 2 ^ w by omega, show m.size + V.size < 2 ^ w by unfold Num.IPM.alphaScale at halphaScaleW; omega,
      show Num.IPM.alphaScale m V < 2 ^ w by omega]
  obtain ⟨s15, c15, v15, r15, hp15, hs15_12, hs15_keep, hc15⟩ :=
    runs_call_of_meetsContract (r := 12) hclog ha15
      (by simpa using (show Num.IPM.alphaScale m V < 2 ^ w by omega))
      ⟨rfl, halphaScaleW, by omega⟩ ω
  obtain ⟨hm15, rfl⟩ := hp15
  have hs15_83 : s15.regs 83 = q := (hs15_keep 83 (by decide)).trans (by simp [s14])
  have hs15_5 : s15.regs 5 = m.size := (hs15_keep 5 (by decide)).trans hs14_5
  have hs15_6 : s15.regs 6 = V.size := (hs15_keep 6 (by decide)).trans hs14_6
  let eps := paramEpsExp threshold A m V
  let sMV := m.size + V.size
  let slack := slackRangeExponent m V
  let qSlack := qualitySlackExponent m V q
  let gradExp := gradientCoefficientExponent m V
  let rangeExp := ipmQualityRangeExponent m V q
  let psi := paramPsi threshold A m V
  have hslack_eq : slack = 220000 * (sMV * sMV) := by simp [slack, slackRangeExponent, sMV, sq]
  have hgrad_eq : gradExp = sMV + 5 := rfl
  have hrange_eq : rangeExp = 4 * qSlack + 2 * gradExp + 100 := rfl
  have hpsi_eq : psi = rangeExp + slack + 6 := rfl
  have hslackW : slack < 2 ^ w := by omega
  have hsMV2W : sMV * sMV < 2 ^ w := by
    have : sMV * sMV ≤ 220000 * (sMV * sMV) := Nat.le_mul_of_pos_left _ (by decide)
    omega
  have hsMVW : sMV < 2 ^ w := by unfold Num.IPM.alphaScale at halphaScaleW; omega
  have hgradW : gradExp < 2 ^ w := by omega
  have hrangeW : rangeExp < 2 ^ w := by omega
  let s16 := { s15 with regs := Function.update s15.regs 84 eps }
  let s17 := { s16 with regs := Function.update s16.regs 13 slack }
  let s18 := { s17 with regs := Function.update s17.regs 14 qSlack }
  let s19 := { s18 with regs := Function.update s18.regs 15 gradExp }
  let s20 := { s19 with regs := Function.update s19.regs 16 rangeExp }
  let s21 := { s20 with regs := Function.update s20.regs 85 psi }
  have heps_eq : eps = q + Nat.clog 2 (Num.IPM.alphaScale m V) + 10 := rfl
  have hepsW' : q + Nat.clog 2 (Num.IPM.alphaScale m V) + 10 < 2 ^ w := hepsW
  have hslackW' : 220000 * ((m.size + V.size) * (m.size + V.size)) < 2 ^ w := by
    simpa [hslack_eq, sMV] using hslackW
  have hsMV2W' : (m.size + V.size) * (m.size + V.size) < 2 ^ w := by
    simpa [sMV] using hsMV2W
  have hsMVW' : m.size + V.size < 2 ^ w := by simpa [sMV] using hsMVW
  have hgradW' : m.size + V.size + 5 < 2 ^ w := by simpa [hgrad_eq, sMV] using hgradW
  have hrangeW' : 4 * qSlack + 2 * gradExp + 100 < 2 ^ w := by simpa [hrange_eq] using hrangeW
  have hpsiW' : rangeExp + slack + 6 < 2 ^ w := hpsiW
  have r16 : Runs w p ω (.assign 84 (.bin .add (.bin .add (.reg 83) (.reg 12)) (.const 10)))
      s15 .normal s16 6 :=
    runs_assign_iff.mpr ⟨eps, by
      simp [Expr.eval, BinOp.eval, hs15_83, hs15_12, heps_eq,
        show 10 < 2 ^ w by omega, show q + Nat.clog 2 (Num.IPM.alphaScale m V) < 2 ^ w by omega,
        hepsW'], rfl, rfl, rfl⟩
  have r17 : Runs w p ω
      (.assign 13 (.bin .mul (.const 220000)
        (.bin .mul (.bin .add (.reg 5) (.reg 6)) (.bin .add (.reg 5) (.reg 6)))))
      s16 .normal s17 10 :=
    runs_assign_iff.mpr ⟨slack, by
      simp [Expr.eval, BinOp.eval, s16, hs15_5, hs15_6, hslack_eq, sMV,
        h220000W, hsMVW', hsMV2W', hslackW'],
      rfl, rfl, rfl⟩
  have hs17_83 : s17.regs 83 = q := by simp [s17, s16, hs15_83]
  have hs17_13 : s17.regs 13 = slack := by simp [s17]
  have r18 : Runs w p ω
      (.cond (.bin .lt (.reg 13) (.reg 83)) (.assign 14 (.reg 83)) (.assign 14 (.reg 13)))
      s17 .normal s18 6 := by
    by_cases hlt : slack < q
    · have hqs : qSlack = q := max_eq_right hlt.le
      refine runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, BinOp.eval, hs17_13, hs17_83, hlt, show 1 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨q, by simp [Expr.eval, hs17_83], rfl, by simp [s18, hqs], rfl⟩, rfl⟩
    · have hqs : qSlack = slack := max_eq_left (by omega)
      refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, hs17_13, hs17_83, hlt, show 0 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨slack, by simp [Expr.eval, hs17_13], rfl, by simp [s18, hqs], rfl⟩, rfl⟩
  have r19 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.reg 5) (.reg 6)) (.const 5)))
      s18 .normal s19 6 :=
    runs_assign_iff.mpr ⟨gradExp, by
      simp [Expr.eval, BinOp.eval, s18, s17, s16, hs15_5, hs15_6, hgrad_eq, sMV, hsMVW',
        show 5 < 2 ^ w by omega, hgradW'], rfl, rfl, rfl⟩
  have r20 : Runs w p ω
      (.assign 16 (.bin .add (.bin .add (.bin .mul (.const 4) (.reg 14))
        (.bin .mul (.const 2) (.reg 15))) (.const 100)))
      s19 .normal s20 10 :=
    runs_assign_iff.mpr ⟨rangeExp, by
      simp [Expr.eval, BinOp.eval, s19, s18, hrange_eq, show 4 < 2 ^ w by omega,
        show 2 < 2 ^ w by omega, show 100 < 2 ^ w by omega,
        show 4 * qSlack < 2 ^ w by omega, show 2 * gradExp < 2 ^ w by omega,
        show 4 * qSlack + 2 * gradExp < 2 ^ w by omega, hrangeW'], rfl, rfl, rfl⟩
  have r21 : Runs w p ω (.assign 85 (.bin .add (.bin .add (.reg 16) (.reg 13)) (.const 6)))
      s20 .normal s21 6 :=
    runs_assign_iff.mpr ⟨psi, by
      simp [Expr.eval, BinOp.eval, s20, s19, s18, s17, hpsi_eq, show 6 < 2 ^ w by omega,
        show rangeExp + slack < 2 ^ w by omega, hpsiW'], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (computeScalarParamsStmt bitLen clog threshold A) st .normal s21
      (2 + (2 + (2 + (6 + (4 + (c6 + (c7 + (c8 + (c9 + (c10 +
        (6 + (8 + (4 + (6 + (c15 + (6 + (10 + (6 + (6 + (10 + 6 + 1) + 1) + 1) + 1) + 1) + 1)
          + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 6, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, c6, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, c7, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, c8, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, c9, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, c10, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 6, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 8, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 4, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 6, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s15, c15, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 6, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s17, 10, _, r17,
    runs_seq_iff.mpr (Or.inr ⟨s18, 6, _, r18,
    runs_seq_iff.mpr (Or.inr ⟨s19, 6, _, r19,
    runs_seq_iff.mpr (Or.inr ⟨s20, 10, 6, r20, r21, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hkeepAll (r : ℕ) (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9)
      (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) (h14 : r ≠ 14) (h15 : r ≠ 15)
      (h16 : r ≠ 16) (h83 : r ≠ 83) (h84 : r ≠ 84) (h85 : r ≠ 85) (h98 : r ≠ 98) :
      s21.regs r = s5.regs r := by
    simp only [s21, s20, s19, s18, s17, s16, Function.update_of_ne h85, Function.update_of_ne h16,
      Function.update_of_ne h15, Function.update_of_ne h14, Function.update_of_ne h13,
      Function.update_of_ne h84]
    rw [hs15_keep r h12]
    simp only [s14, s13, s12, s11, Function.update_of_ne h83, Function.update_of_ne h11,
      Function.update_of_ne h10, Function.update_of_ne h98]
    exact hkeep10 r h5 h6 h7 h8 h9
  have hmem21 : s21.mem = st.mem := by
    change s15.mem = st.mem
    rw [hm15]; change s10.mem = st.mem
    rw [hm10, hm9, hm8, hm7, hm6]
  simp only [Num.IPM.bitLengthContract, Scaling.Machine.clogTwoContract, argsSize, Expr.size,
    List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some] at hc6 hc7 hc8 hc9 hc10 hc15
  refine ⟨s21, _, rFull,
    (hkeepAll 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1, h0]),
    (hkeepAll 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (by simp [s5, s4]),
    (hkeepAll 80 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1]),
    (hkeepAll 81 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3, s2]),
    (hkeepAll 82 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (by simp [s5, s4, s3]),
    by simp [s21, s20, s19, s18, s17, s16, hs15_83, q],
    by simp [s21, s20, s19, s18, s17, s16, eps],
    by simp [s21, psi],
    (hkeepAll 86 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (by simp [s5, paramN0, M₀, paramM0]),
    by simp [s21, s20, s19, s18, s17, s16, hs15_keep 98 (by decide), s14, s13, s12, s11],
    hmem21, ?_⟩
  unfold scalarParamsCost Num.IPM.alphaExponent
  omega


end MinCostFlow.MinRatio

end
