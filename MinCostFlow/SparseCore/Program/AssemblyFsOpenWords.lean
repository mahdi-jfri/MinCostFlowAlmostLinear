module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4Defs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpaceTotal

import Mathlib.Tactic

/-!
# Spanner word-size bounds from the standard first-step space (`AssemblyFsOpenWords`)

Under `AsmFsPre` instantiated at the standard monotone step-space function
`asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp` (`AssemblyFirstStepSpaceTotal.lean`), the room
hypothesis `A.h + asmFirstStepSpaceFnStd ... < 2 ^ w` implies the word-size bounds needed by both
Phase 4's per-slot `DSUpdatePre` (`AssemblyFsOpen.lean`) and the post-step side-model preservation
(`asmBrSideModel_step` in `hPost`):
* `(36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w`,
* `10 * (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 * (depth + 7) < 2 ^ w`, and
* `A.x.xRest.spV + A.x.xRest.spE + 2 < 2 ^ w`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

private lemma one_le_lenBoundLinearConst (C_sp : ℝ) : 1 ≤ lenBoundLinearConst C_sp := by
  unfold lenBoundLinearConst
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.exp_pos _)).ne'

private lemma asmFirstStepSpacePolyStd_coeff_ge (c₀ cw capExp : ℕ) (C_sp : ℝ) :
    3312 * 149040 ^ cw ≤ (asmFirstStepSpacePolyStd c₀ cw capExp C_sp).coeff := by
  unfold asmFirstStepSpacePolyStd asmFirstStepSpacePolySub asmFirstStepSpacePoly
    asmFirstPhase4SpacePoly
  dsimp only
  have hL : 1 ≤ lenBoundLinearConst C_sp := one_le_lenBoundLinearConst C_sp
  have h1 : 149040 ^ cw ≤ (149040 * lenBoundLinearConst C_sp) ^ cw :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_right 149040 hL) cw
  have h2 : 3312 * 149040 ^ cw ≤ 3312 * (149040 * lenBoundLinearConst C_sp) ^ cw :=
    Nat.mul_le_mul_left 3312 h1
  omega

private lemma asmFirstStepSpacePolyStd_deg_eq (c₀ cw capExp : ℕ) (C_sp : ℝ) :
    (asmFirstStepSpacePolyStd c₀ cw capExp C_sp).deg = (capExp + 7) * (4 * cw + 13) := by
  unfold asmFirstStepSpacePolyStd asmFirstStepSpacePolySub asmFirstStepSpacePoly
  dsimp only
  ring

private lemma wordBounds_arith {spV spE depth cw capExp Z W : ℕ}
    (hZ2 : 2 ≤ Z) (hdZ : depth ≤ Z)
    (hsp : spV + spE + 2 ≤ Z ^ (capExp + 7))
    (hBound : 3312 * 149040 ^ cw * Z ^ ((capExp + 7) * (4 * cw + 13)) < W) :
    (36 * (spV + 2 * spE + 1)) ^ cw < W ∧
    10 * (spV + spE + 2) ^ 2 * (depth + 7) < W := by
  generalize hBdef : Z ^ (capExp + 7) = B at hsp
  have hZpos : 0 < Z := by omega
  have hZ_B : Z ≤ B := hBdef ▸ Nat.le_self_pow (by omega) Z
  have h1 : (36 * (spV + 2 * spE + 1)) ^ cw < W := by
    have hbase : 36 * (spV + 2 * spE + 1) ≤ 149040 * B := by omega
    have hpow : (36 * (spV + 2 * spE + 1)) ^ cw ≤ 149040 ^ cw * B ^ cw := by
      calc (36 * (spV + 2 * spE + 1)) ^ cw
          ≤ (149040 * B) ^ cw := Nat.pow_le_pow_left hbase cw
        _ = 149040 ^ cw * B ^ cw := Nat.mul_pow 149040 B cw
    have hBcw : B ^ cw ≤ Z ^ ((capExp + 7) * (4 * cw + 13)) := by
      rw [← hBdef, ← pow_mul]
      exact Nat.pow_le_pow_right hZpos (Nat.mul_le_mul_left (capExp + 7) (by omega))
    have hle : (36 * (spV + 2 * spE + 1)) ^ cw ≤
        3312 * 149040 ^ cw * Z ^ ((capExp + 7) * (4 * cw + 13)) := by
      calc (36 * (spV + 2 * spE + 1)) ^ cw
          ≤ 149040 ^ cw * B ^ cw := hpow
        _ ≤ 149040 ^ cw * Z ^ ((capExp + 7) * (4 * cw + 13)) :=
            Nat.mul_le_mul_left _ hBcw
        _ ≤ 3312 * (149040 ^ cw * Z ^ ((capExp + 7) * (4 * cw + 13))) :=
            Nat.le_mul_of_pos_left _ (by decide)
        _ = 3312 * 149040 ^ cw * Z ^ ((capExp + 7) * (4 * cw + 13)) := (Nat.mul_assoc _ _ _).symm
    exact lt_of_le_of_lt hle hBound
  have h2 : 10 * (spV + spE + 2) ^ 2 * (depth + 7) < W := by
    have hdB : depth + 7 ≤ 7 * B := by omega
    have hB3 : B ^ 3 ≤ Z ^ ((capExp + 7) * (4 * cw + 13)) := by
      rw [← hBdef, ← pow_mul]
      exact Nat.pow_le_pow_right hZpos (Nat.mul_le_mul_left (capExp + 7) (by omega))
    have hpow1 : 1 ≤ 149040 ^ cw := Nat.one_le_pow _ _ (by decide)
    have hle : 10 * (spV + spE + 2) ^ 2 * (depth + 7) ≤
        3312 * 149040 ^ cw * Z ^ ((capExp + 7) * (4 * cw + 13)) := by
      calc 10 * (spV + spE + 2) ^ 2 * (depth + 7)
          ≤ 10 * B ^ 2 * (7 * B) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left hsp 2)) hdB
        _ = 70 * B ^ 3 := by ring
        _ ≤ 3312 * B ^ 3 := Nat.mul_le_mul_right _ (by decide)
        _ ≤ 3312 * 149040 ^ cw * B ^ 3 :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right 3312 hpow1)
        _ ≤ 3312 * 149040 ^ cw * Z ^ ((capExp + 7) * (4 * cw + 13)) :=
            Nat.mul_le_mul_left _ hB3
    exact lt_of_le_of_lt hle hBound
  exact ⟨h1, h2⟩

public section

/-- **Core word-size bounds from `asmFirstStepSpaceFnStd`.** Under `AsmFsPre` with
`space := asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp`, the room inequality
`A.h + space (M + N + k + vCap + eCap + L + depth + words + editWords) < 2 ^ w` implies both
`(36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w` and
`10 * (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 * (depth + 7) < 2 ^ w`. -/
theorem asmFirstStep_wordBounds_of_spaceStd {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ} :
    ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
        (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A →
      (36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w ∧
      10 * (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 * (depth + 7) < 2 ^ w := by
  intro A hA
  unfold AsmFsPre AsmFsPreRaw at hA
  obtain ⟨hM, hN, -, -, -, -, -, -, -, hR, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hspace, -⟩ := hA
  have hCapSp : A.x.xRest.spV + A.x.xRest.spE + 2 ≤ (A.M + A.N + 2) ^ (capExp + 7) := by
    have hSide := hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hMod := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hSc := hMod.2.2.2.2.2.2.2.2.2.2.1.1
    rw [hM, hN] at hSc
    exact hSc
  set X := A.M + A.N + A.k + A.x.vCap + A.x.eCap + L + depth + A.words + A.editWords
  have hSp_lt : (asmFirstStepSpacePolyStd c₀ impl.cw capExp C_sp).eval X < 2 ^ w := by
    unfold asmFirstStepSpaceFnStd at hspace
    exact lt_of_le_of_lt (Nat.le_add_left _ A.h) hspace
  have hEval_ge : 3312 * 149040 ^ impl.cw * (X + 2) ^ ((capExp + 7) * (4 * impl.cw + 13)) ≤
      (asmFirstStepSpacePolyStd c₀ impl.cw capExp C_sp).eval X := by
    unfold PolyBound.eval
    rw [asmFirstStepSpacePolyStd_deg_eq c₀ impl.cw capExp C_sp]
    exact Nat.mul_le_mul_right _ (asmFirstStepSpacePolyStd_coeff_ge c₀ impl.cw capExp C_sp)
  have hsp_Z : A.x.xRest.spV + A.x.xRest.spE + 2 ≤ (X + 2) ^ (capExp + 7) :=
    hCapSp.trans (Nat.pow_le_pow_left (by omega) (capExp + 7))
  exact wordBounds_arith (by omega) (by omega) hsp_Z (lt_of_le_of_lt hEval_ge hSp_lt)

/-- **Side-model word bounds for `hPost` (`asmBrSideModel_step`) from `asmFirstStepSpaceFnStd`.**
Direct projection of `asmFirstStep_wordBounds_of_spaceStd` giving the exact two word bounds
`hw : y.spV + y.spE + 2 < 2 ^ w` and `hcw : (36 * (y.spV + 2 * y.spE + 1)) ^ impl.cw < 2 ^ w`
required by `asmBrSideModel_step` (`AssemblyFirstStepSideStep.lean:497-498`). -/
theorem asmFirstStep_sideWordBounds_of_spaceStd {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ} :
    ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
        (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A →
      A.x.xRest.spV + A.x.xRest.spE + 2 < 2 ^ w ∧
      (36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w := by
  intro A hA
  obtain ⟨h1, h2⟩ := asmFirstStep_wordBounds_of_spaceStd A hA
  have hle : A.x.xRest.spV + A.x.xRest.spE + 2 ≤
      10 * (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 * (depth + 7) := by
    have hsq : A.x.xRest.spV + A.x.xRest.spE + 2 ≤ (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 := by
      nlinarith
    have hmul : (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 ≤
        10 * (A.x.xRest.spV + A.x.xRest.spE + 2) ^ 2 * (depth + 7) := by
      nlinarith
    omega
  exact ⟨lt_of_le_of_lt hle h2, h1⟩

end

end MinCostFlow.SparseCore.Program
