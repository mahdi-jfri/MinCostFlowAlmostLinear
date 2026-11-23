module

public import MinCostFlow.ExpanderDecomp.OuterProgRec
public import MinCostFlow.ExpanderDecomp.Used
public import MinCostFlow.ExpanderDecomp.RouteMeets
public import MinCostFlow.ExpanderDecomp.OuterProgParams
public import MinCostFlow.ExpanderDecomp.OuterProgGame
public import MinCostFlow.ExpanderDecomp.OuterProgMatching
public import MinCostFlow.ExpanderDecomp.OuterProgPortOps
public import MinCostFlow.ExpanderDecomp.OuterProgSubgraphOps
public import MinCostFlow.ExpanderDecomp.ProgRemoveFake
public import MinCostFlow.ExpanderDecomp.ProgCompLabels
public import MinCostFlow.ExpanderDecomp.ProgPortGraph

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Top-Level Outer Expander Decomposition Module (`OuterProgMain`)

Assembles the complete deterministic (`NoRand`) Word-RAM outer expander-decomposition module:

1. `outerDecompMainProc`: entry procedure taking `[gAddr, r, outAddr, h]` (`ProgDecompEntrySpec`),
   reading `n = mem[gAddr]` and `M = mem[gAddr + 1]`, laying out the root parameter block, zeroed
   scratch array `locAddr`, label counter `nextLblAddr`, initial vertex list `[0, ..., n - 1]`, and
   active-vertex buffer inside `[h, h + 13 + 3 * n)`, invoking `computeParamsProc`,
   `stripIsolatedProc`, and `outerDecompRecProc`, and returning `0`.
2. `outerDecompProcs (base coreAdapterIdx routeIdx : ℕ)`: self-contained relocatable bundle of all
   outer decomposition procedures, calling the external outer-to-core adapter at `coreAdapterIdx`
   (`CoreOuter.coreAdapterContract`) and the static router at `routeIdx`
   (`OuterProgContracts.routeOrCutContract`).
3. `outerDecompMainProc_spec`: proves `outerDecompProcs` placed at `base` meets
   `ProgDecompEntrySpec.outerDecompEntryContract (outerDecompK C_core C_rt) (outerDecompSpaceC C_sp) w`
   for every word size `w`.
4. `outerDecompModule`: concrete instance of `Used.OuterDecompModule K_B C_rt S_B C_sp_rt`, together
   with determinism `outerDecompProcs_noRand` and the top-level entry corollary `outerDecomp_runsTo`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 1. Procedure Indices, Top-Level Procedure, and Relocatable Bundle -/

/-- Procedure index table for `outerDecompMainProc`. -/
structure OuterMainIndices where
  /-- Index of `computeParamsProc ParamConfig.default`. -/
  bParams : ℕ
  /-- Index of `stripIsolatedProc`. -/
  bStripIso : ℕ
  /-- Index of `outerDecompRecProc`. -/
  bRec : ℕ

/-- Fills `mem[r9 + i] := i` for `0 ≤ i < r4`, using loop counter `r11`. -/
def fillRangeStmt : Stmt :=
  forRange 11 (.const 0) (.reg 4) (.store (.bin .add (.reg 9) (.reg 11)) (.reg 11))

/-- Top-level outer expander-decomposition procedure.
Args: `[gAddr, r, outAddr, h]` in registers `r0..r3`.
Allocates `[h, h + 13 + 3 * n)` for `paramAddr` (12), `locAddr` (`n`), `nextLblAddr` (1),
`verts0Addr` (`n`), and `actVertsAddr` (`n`), computes parameters, strips root isolated vertices,
and invokes the recursive outer decomposition procedure. -/
def outerDecompMainProc (idx : OuterMainIndices) : Stmt :=
  (.assign 4 (.load (.reg 0)) ;;
   .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
   .assign 6 (.bin .add (.reg 0) (.const 2)) ;;
   .assign 7 (.reg 3) ;;
   .assign 8 (.bin .add (.reg 7) (.const 12))) ;;
  (.assign 12 (.bin .add (.reg 8) (.reg 4)) ;;
   .assign 9 (.bin .add (.reg 12) (.const 1)) ;;
   .assign 10 (.bin .add (.reg 9) (.reg 4)) ;;
   .assign 13 (.bin .add (.reg 10) (.reg 4))) ;;
  .call 14 idx.bParams [.reg 4, .reg 5, .reg 1, .reg 7] ;;
  fillRangeStmt ;;
  .call 14 idx.bStripIso [.reg 4, .reg 9, .reg 5, .reg 6, .reg 8, .reg 2, .reg 12, .reg 10] ;;
  .call 13 idx.bRec [.reg 14, .reg 10, .reg 5, .reg 6, .reg 7, .reg 8, .reg 2, .reg 12, .reg 13] ;;
  .ret (.const 0)

/-- Subprocedure indices for `outerGameProc` inside `outerDecompProcs base coreAdapterIdx routeIdx`. -/
def outerGameIndicesOf (base coreAdapterIdx routeIdx : ℕ) : OuterGameIndices where
  bCoreLevel := base + 2
  bCore := coreAdapterIdx
  bRoute := routeIdx
  bPad := base + 8
  bInj := base + 9
  bFake := base + 10

/-- Subprocedure indices for `outerDecompRecProc` inside `outerDecompProcs base _ _`. -/
def outerRecIndicesOf (base : ℕ) : OuterRecIndices where
  bSelf := base + 12
  bComp := base + 16
  bPort := base + 16 + (compLabelsInProcs (base + 16)).length
  bGame := base + 11
  bRound := base + 7
  bRestrict := base + 4
  bStripIso := base + 3
  bContract := base + 6
  bRF := base + 13
  bSetDiff := base + 5

/-- Subprocedure indices for `outerDecompMainProc` inside `outerDecompProcs base _ _`. -/
def outerMainIndicesOf (base : ℕ) : OuterMainIndices where
  bParams := base + 1
  bStripIso := base + 3
  bRec := base + 12

/-- Self-contained relocatable Word-RAM procedure bundle implementing the outer expander
decomposition. When installed at `base` with external `coreAdapterContract` at `coreAdapterIdx`
and `routeOrCutContract` at `routeIdx`, entry procedure `base` meets `outerDecompEntryContract`. -/
def outerDecompProcs (base coreAdapterIdx routeIdx : ℕ) : List Stmt :=
  [ outerDecompMainProc (outerMainIndicesOf base)
  , computeParamsProc ParamConfig.default
  , coreLevelProc
  , stripIsolatedProc
  , restrictProc
  , setDiffProc
  , outerContractEdgesProc
  , outerRoundPortCutProc
  , padToBisectionProc
  , buildInjPairProc
  , fakeCompletionProc
  , outerGameProc (outerGameIndicesOf base coreAdapterIdx routeIdx)
  , outerDecompRecProc (outerRecIndicesOf base)
  ] ++ removeFakeProcs (base + 13) ++ compLabelsInProcs (base + 16) ++
    portGraphProcs (base + 16 + (compLabelsInProcs (base + 16)).length)

/-- Input-independent step-count multiplier `K` for `outerDecompEntryContract`. -/
def outerDecompK (C_core C_rt : ℕ) : ℕ :=
  outerRecCostK C_core C_rt 80 + 2000

/-- Input-independent heap-space multiplier `C_sp` for `outerDecompEntryContract`. -/
def outerDecompSpaceC (C_sp : ℕ) : ℕ :=
  outerRecSpaceC C_sp 80

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 2. Determinism (`NoRand`) -/

lemma fillRangeStmt_noRand : fillRangeStmt.NoRand := by
  simp [fillRangeStmt, forRange, forUp, Stmt.NoRand]

theorem outerDecompMainProc_noRand (idx : OuterMainIndices) : (outerDecompMainProc idx).NoRand := by
  simp [outerDecompMainProc, fillRangeStmt_noRand, Stmt.NoRand]

theorem outerDecompProcs_noRand (base coreAdapterIdx routeIdx : ℕ) :
    ∀ s ∈ outerDecompProcs base coreAdapterIdx routeIdx, s.NoRand := by
  intro s hs
  unfold outerDecompProcs at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hRF) | hComp) | hPort
  · exact outerDecompMainProc_noRand _
  · exact computeParamsProc_noRand _
  · exact coreLevelProc_noRand
  · exact stripIsolatedProc_noRand
  · exact restrictProc_noRand
  · exact setDiffProc_noRand
  · exact outerContractEdgesProc_noRand
  · exact outerRoundPortCutProc_noRand
  · exact padToBisectionProc_noRand
  · exact buildInjPairProc_noRand
  · exact fakeCompletionProc_noRand
  · exact outerGameProc_noRand _
  · exact outerDecompRecProc_noRand _
  · exact removeFakeProcs_noRand _ s hRF
  · exact compLabelsInProcs_noRand _ s hComp
  · exact portGraphProcs_noRand _ s hPort

/-! ## 3. Arithmetic and Word-Bound Helpers -/

lemma qOut_add_le_totalTimeRaw {n M : ℕ} (hM4 : 4 ≤ M) :
    let r := rOf M
    QOut ParamConfig.default M r + 16 ≤ totalTimeRaw ParamConfig.default n M r ∧
    NOf M r * (2 * M) + 16 ≤ totalTimeRaw ParamConfig.default n M r ∧
    bOut ParamConfig.default M ≤ totalTimeRaw ParamConfig.default n M r ∧
    4 * M + 32 ≤ totalTimeRaw ParamConfig.default n M r ∧
    n + 16 ≤ totalTimeRaw ParamConfig.default n M r ∧
    1920 * ParamConfig.default.a₀ + 16 ≤ totalTimeRaw ParamConfig.default n M r ∧
    16 * ParamConfig.default.kappa * ParamConfig.default.E + 16 ≤ totalTimeRaw ParamConfig.default n M r ∧
    16 * ParamConfig.default.A + 16 ≤ totalTimeRaw ParamConfig.default n M r ∧
    250 < totalTimeRaw ParamConfig.default n M r := by
  intro r
  set cfg := ParamConfig.default
  set L := LParam M
  set Λ := Lambda cfg M r
  set t := tParam M
  set b := bOut cfg M
  set H := HDepth cfg M r
  set A := (t + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)
  set B := t * b ^ 3 * L ^ 3
  set inner := n + M * H * (A + B + L) + M * Λ ^ 2 * L ^ 2
  have hTot_eq : totalTimeRaw cfg n M r = cfg.CTotal * inner := rfl
  have hCT : cfg.CTotal = 2 ^ 40 := by decide
  have hL4 : 4 ≤ L := four_le_LParam M
  have hLam1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hb1 : 1 ≤ b := one_le_bOut cfg M
  have hH1 : 1 ≤ H := by unfold H HDepth; omega
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hW1 : 1 ≤ WParam cfg M := by unfold WParam; omega
  have hinner_pos : 1 ≤ inner := by
    have : 1 ≤ M * Λ ^ 2 * L ^ 2 :=
      Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos hLam1)) (Nat.pow_pos (by omega))
    omega
  have htot_ge_c40 : 2 ^ 40 ≤ totalTimeRaw cfg n M r := by
    rw [hTot_eq, hCT]; exact Nat.le_mul_of_pos_right _ hinner_pos
  have hQ_le : QOut cfg M r + 16 ≤ totalTimeRaw cfg n M r := by
    have htb_sq : (t * b) ^ 2 ≤ 1024 * B := by
      have ht_eq : t = 1024 * L := rfl
      have h1 : (t * b) ^ 2 = 1024 * (t * b ^ 2 * L) := by rw [ht_eq]; ring
      have h2 : t * b ^ 2 * L ≤ t * b ^ 3 * L ^ 3 := by
        have hb23 : b ^ 2 ≤ b ^ 3 := by
          have : b ^ 3 = b ^ 2 * b := by ring
          rw [this]; exact Nat.le_mul_of_pos_right _ hb1
        have hL13 : L ≤ L ^ 3 := by
          have : L ^ 3 = L * (L * L) := by ring
          rw [this]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
        calc t * b ^ 2 * L ≤ t * b ^ 3 * L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left t hb23)
          _ ≤ t * b ^ 3 * L ^ 3 := Nat.mul_le_mul_left _ hL13
      dsimp only [B]; omega
    have hamgm : t * Λ * b ≤ Λ ^ 2 + (t * b) ^ 2 := by
      rcases le_total Λ (t * b) with h | h
      · have h1 : t * Λ * b = Λ * (t * b) := by ring
        have h2 : (t * b) * (t * b) = (t * b) ^ 2 := (sq (t * b)).symm
        rw [h1]; exact le_trans (Nat.mul_le_mul_right (t * b) h) (by rw [h2]; exact Nat.le_add_left _ _)
      · have h1 : t * Λ * b = (t * b) * Λ := by ring
        have h2 : Λ * Λ = Λ ^ 2 := (sq Λ).symm
        rw [h1]; exact le_trans (Nat.mul_le_mul_right Λ h) (by rw [h2]; exact Nat.le_add_right _ _)
    have hLam2_in : Λ ^ 2 ≤ inner := by
      have : Λ ^ 2 ≤ M * Λ ^ 2 * L ^ 2 := by
        calc Λ ^ 2 = 1 * Λ ^ 2 * 1 := by ring
          _ ≤ M * Λ ^ 2 * L ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (Nat.pow_pos (by omega))
      omega
    have hB_in : B ≤ inner := by
      have : B ≤ M * H * (A + B + L) := by
        calc B = 1 * 1 * B := by ring
          _ ≤ M * H * (A + B + L) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) hH1) (by omega)
      omega
    have hprod_le : t * Λ * b ≤ 1025 * inner := by linarith
    have hQ_eq : QOut cfg M r = 2 * (16 * cfg.A * t * Λ * b) + 2 := rfl
    have hA_val : cfg.A = 240 := by decide
    have hQ_bound : QOut cfg M r + 16 ≤ 7680 * (1025 * inner) + 18 := by
      have h1 : 2 * (16 * cfg.A * t * Λ * b) = 7680 * (t * Λ * b) := by rw [hA_val]; ring
      have h2 : 7680 * (t * Λ * b) ≤ 7680 * (1025 * inner) := Nat.mul_le_mul_left 7680 hprod_le
      omega
    have hcoeff : 7680 * 1025 + 18 ≤ 2 ^ 40 := by decide
    rw [hTot_eq, hCT]
    have h1 : 7680 * (1025 * inner) + 18 ≤ (7680 * 1025 + 18) * inner := by
      have : (7680 * 1025 + 18) * inner = 7680 * (1025 * inner) + 18 * inner := by ring
      have : 18 ≤ 18 * inner := Nat.le_mul_of_pos_right 18 hinner_pos
      linarith
    exact le_trans hQ_bound (le_trans h1 (Nat.mul_le_mul_right inner hcoeff))
  have hN2M_le : NOf M r * (2 * M) + 16 ≤ totalTimeRaw cfg n M r := by
    have hN2_le_A : (NOf M r) ^ 2 ≤ A := by
      have : (NOf M r) ^ 2 = 1 * (NOf M r) ^ 2 * 1 := by ring
      rw [this]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (Nat.pow_pos hW1)
    have hNM_in : NOf M r * M ≤ inner := by
      have h1 : NOf M r ≤ (NOf M r) ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
      have h2 : NOf M r * M ≤ M * H * (A + B + L) := by
        calc NOf M r * M = M * 1 * NOf M r := by ring
          _ ≤ M * H * (A + B + L) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left M hH1) (le_trans h1 (le_trans hN2_le_A (by omega)))
      omega
    rw [hTot_eq, hCT]
    have h1 : NOf M r * (2 * M) = 2 * (NOf M r * M) := by ring
    have h2 : 2 * (NOf M r * M) + 16 ≤ 2 ^ 40 * inner := by
      have : 16 ≤ 16 * inner := Nat.le_mul_of_pos_right 16 hinner_pos
      have : 2 * inner + 16 * inner ≤ 2 ^ 40 * inner := by
        have h18 : 2 + 16 ≤ 2 ^ 40 := by decide
        have := Nat.mul_le_mul_right inner h18
        linarith
      linarith
    omega
  have hb_le : b ≤ totalTimeRaw cfg n M r := by
    have hb_B : b ≤ B := by
      have hb3 : b ≤ b ^ 3 := by
        have : b ^ 3 = b * (b * b) := by ring
        rw [this]; exact Nat.le_mul_of_pos_right _ (by nlinarith)
      have ht1 : 1 ≤ t := by unfold t tParam; omega
      have hL3 : 1 ≤ L ^ 3 := Nat.pow_pos (by omega)
      calc b = 1 * b * 1 := by ring
        _ ≤ t * b ^ 3 * L ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul ht1 hb3) hL3
    have hb_in : b ≤ inner := by
      have : B ≤ M * H * (A + B + L) := by
        calc B = 1 * 1 * B := by ring
          _ ≤ M * H * (A + B + L) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hH1) (by omega)
      omega
    rw [hTot_eq, hCT]
    exact le_trans hb_in (Nat.le_mul_of_pos_left inner (by decide))
  have h4M_le : 4 * M + 32 ≤ totalTimeRaw cfg n M r := by
    have hM_in : M ≤ inner := by
      have : M ≤ M * Λ ^ 2 * L ^ 2 := by
        calc M = M * 1 * 1 := by ring
          _ ≤ M * Λ ^ 2 * L ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left M (Nat.pow_pos hLam1)) (Nat.pow_pos (by omega))
      omega
    rw [hTot_eq, hCT]
    have h1 : 32 ≤ 32 * inner := Nat.le_mul_of_pos_right 32 hinner_pos
    have h36 : 4 + 32 ≤ 2 ^ 40 := by decide
    have h2 := Nat.mul_le_mul_right inner h36
    linarith
  have hn16_le : n + 16 ≤ totalTimeRaw cfg n M r := by
    have hn_in : n ≤ inner := by omega
    rw [hTot_eq, hCT]
    have h1 : 16 ≤ 16 * inner := Nat.le_mul_of_pos_right 16 hinner_pos
    have h17 : 1 + 16 ≤ 2 ^ 40 := by decide
    have h2 := Nat.mul_le_mul_right inner h17
    linarith
  refine ⟨hQ_le, hN2M_le, hb_le, h4M_le, hn16_le, ?_, ?_, ?_, ?_⟩
  · exact le_trans (by decide : 1920 * cfg.a₀ + 16 ≤ 2 ^ 40) htot_ge_c40
  · exact le_trans (by decide : 16 * cfg.kappa * cfg.E + 16 ≤ 2 ^ 40) htot_ge_c40
  · exact le_trans (by decide : 16 * cfg.A + 16 ≤ 2 ^ 40) htot_ge_c40
  · exact lt_of_lt_of_le (by decide : 250 < 2 ^ 40) htot_ge_c40

lemma totalTimeRaw_le_outerDecompSpace (C_sp n M tot : ℕ) :
    tot + 1 ≤ outerDecompSpace (outerDecompSpaceC C_sp) n M tot := by
  unfold outerDecompSpace outerDecompSpaceC outerRecSpaceC
  have h1 : 1 ≤ C_sp * 2 ^ 155 * (80 * 2 ^ 29 + 300) + C_sp * 3600 + 46000 := by
    omega
  have h2 : 1 ≤ (n + M + 3) ^ 6 := Nat.pow_pos (by omega)
  calc tot + 1 = 1 * (tot + 1) * 1 := by ring
    _ ≤ (C_sp * 2 ^ 155 * (80 * 2 ^ 29 + 300) + C_sp * 3600 + 46000) *
          (tot + 1) * (n + M + 3) ^ 6 :=
        Nat.mul_le_mul (Nat.mul_le_mul_right (tot + 1) h1) h2

lemma topLevelOverhead_le {n M : ℕ} (hM4 : 4 ≤ M) :
    let r := rOf M
    computeParamsCost M r + (14 * n + 20) + stripIsolatedCost n M + 1500 ≤
      2000 * totalTimeRaw ParamConfig.default n M r + 1400 := by
  intro r
  set cfg := ParamConfig.default
  set L := LParam M
  set Λ := Lambda cfg M r
  set H := HDepth cfg M r
  set A := (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)
  set B := tParam M * (bOut cfg M) ^ 3 * L ^ 3
  set inner := n + M * H * (A + B + L) + M * Λ ^ 2 * L ^ 2
  have hCT : cfg.CTotal = 2 ^ 40 := by decide
  have hL4 : 4 ≤ L := four_le_LParam M
  have hLam1 : 1 ≤ Λ := one_le_Lambda cfg M r
  have hH1 : 1 ≤ H := by unfold H HDepth; omega
  have hr_le_ell : r ≤ ell M := rOf_le_ell M
  have hell_le_L : ell M ≤ L := by unfold L LParam; omega
  have hL_in : L ≤ inner := by
    have : L ≤ M * H * (A + B + L) := by
      calc L = 1 * 1 * L := by ring
        _ ≤ M * H * (A + B + L) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hH1) (by omega)
    omega
  have hM_in : M ≤ inner := by
    have : M ≤ M * Λ ^ 2 * L ^ 2 := by
      calc M = M * 1 * 1 := by ring
        _ ≤ M * Λ ^ 2 * L ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left M (Nat.pow_pos hLam1)) (Nat.pow_pos (by omega))
    omega
  have hn_in : n ≤ inner := by omega
  have hinner_pos : 1 ≤ inner := by omega
  have htot_eq : totalTimeRaw cfg n M r = 2 ^ 40 * inner := by
    unfold totalTimeRaw; rw [hCT]
  unfold computeParamsCost stripIsolatedCost
  have hsum : 60 * (ell M + r + 1) + 500 + (14 * n + 20) + (60 * n + 120 * M + 80) + 1500 ≤
      120 * L + 74 * n + 120 * M + 2160 := by omega
  have hle_in : 120 * L + 74 * n + 120 * M + 2160 ≤ 2500 * inner := by
    have : 2160 ≤ 2160 * inner := Nat.le_mul_of_pos_right 2160 hinner_pos
    linarith
  have h2500 : 2500 ≤ 2000 * 2 ^ 40 := by decide
  have h3 := Nat.mul_le_mul_right inner h2500
  rw [htot_eq]
  linarith

/-! ## 4. `fillRangeStmt` Specification and Subprocedure Extraction -/

lemma fillRange_triple {w n vertsAddr : ℕ} (p : Program) (st₀ : State)
    (hr4 : st₀.regs 4 = n) (hr9 : st₀.regs 9 = vertsAddr)
    (hvw : vertsAddr + n < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    Triple w p (fun s => s = st₀) fillRangeStmt
      (normalPost fun s' =>
        ListAt s'.mem vertsAddr (List.range n) ∧
        (∀ a, a < vertsAddr ∨ vertsAddr + n ≤ a → s'.mem a = st₀.mem a) ∧
        (∀ r', r' ≠ 11 → s'.regs r' = st₀.regs r'))
      (fun _ => 14 * n + 20) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hLoop := Triple.forRange_const (p := p) (r := 11) (lo := .const 0) (hi := .reg 4)
    (body := .store (.bin .add (.reg 9) (.reg 11)) (.reg 11))
    (P := fun s => s = st₀)
    (Inv := fun k s =>
      s.regs 11 = k ∧
      (∀ r', r' ≠ 11 → s.regs r' = st₀.regs r') ∧
      (∀ j < k, s.mem (vertsAddr + j) = j) ∧
      (∀ a, a < vertsAddr ∨ vertsAddr + n ≤ a → s.mem a = st₀.mem a))
    5 0 n (Nat.zero_le n) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r' hr' => by simp [Function.update_of_ne hr'],
        fun _ hj => by omega, fun _ _ => rfl⟩)
    (fun _ s _ _ hI => hI.1)
    (fun _ s _ _ ⟨_, hkr, _, _⟩ => by
      have hr4' : s.regs 4 = n := by rw [hkr 4 (by decide), hr4]
      simp [Expr.eval, hr4'])
    (fun j _ hj => by
      intro s ω ⟨h11, hkr, hdone, hfr⟩
      refine runs_start_le ?_
      refine runs_store_le (x := vertsAddr + j) (v := j)
        (by simp [Expr.eval, BinOp.eval, hkr 9 (by decide), hr9, h11, (by omega : vertsAddr + j < 2 ^ w)])
        (by simp [Expr.eval, h11]) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, fun r' hr' => by simp [Function.update_of_ne hr', hkr r' hr'],
        fun i hi => by
          dsimp only
          by_cases heq : i = j
          · subst heq; simp
          · rw [Function.update_of_ne (by omega)]; exact hdone i (by omega),
        fun a ha => by
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hfr a ha⟩,
        h11⟩)
  refine hLoop.conseq (fun _ h => h)
    (fun o s' hq => by
      cases o with
      | returned _ => exact False.elim hq
      | normal =>
        rcases hq with ⟨_, hkr, hdone, hfr⟩
        exact ⟨fun i hi => by
          have hi' : i < n := by simpa using hi
          rw [List.getElem_range]; exact hdone i hi', hfr, hkr⟩)
    (fun _ _ => by simp [Expr.size]; omega)

private lemma hasAt_slice_outer {p : Program} {base : ℕ} {seg : List Stmt}
    (hHas : p.HasAt base seg) {off : ℕ} {sub : List Stmt}
    (hsub : ∀ i (hi : i < sub.length), seg[off + i]? = some sub[i]) :
    p.HasAt (base + off) sub := by
  intro i hi
  have hlen : off + i < seg.length := by
    by_contra hge
    have hnone : seg[off + i]? = none := List.getElem?_eq_none (by omega)
    have hsome := hsub i hi
    rw [hnone] at hsome; cases hsome
  have h1 := hHas (off + i) hlen
  have h2 := hsub i hi
  rw [List.getElem?_eq_getElem hlen] at h2
  have h3 : seg[off + i] = sub[i] := Option.some.inj h2
  rw [Nat.add_assoc, h1, h3]

private lemma hasAt_single_outer {p : Program} {base : ℕ} {seg : List Stmt}
    (hHas : p.HasAt base seg) {off : ℕ} {s : Stmt}
    (hs : seg[off]? = some s) :
    p.procs[base + off]? = some s := by
  have hlen : off < seg.length := by
    by_contra hge
    have hnone : seg[off]? = none := List.getElem?_eq_none (by omega)
    rw [hnone] at hs; cases hs
  have h1 := hHas off hlen
  rw [List.getElem?_eq_getElem hlen] at hs
  rw [h1, Option.some.inj hs]

private lemma hasAt_singleton_outer {p : Program} {base : ℕ} {seg : List Stmt}
    (hHas : p.HasAt base seg) {off : ℕ} {s : Stmt}
    (hs : seg[off]? = some s) :
    p.HasAt (base + off) [s] := by
  intro i hi
  cases i with
  | zero => simpa using hasAt_single_outer hHas hs
  | succ _ => simp at hi

lemma outerDecompProcs_subprocs
    {base coreAdapterIdx routeIdx M r w C_core C_rt C_sp_core C_sp_rt C_sp : ℕ}
    {coreCost : ℕ → Graph → ℕ} {p : Program}
    (hHas : p.HasAt base (outerDecompProcs base coreAdapterIdx routeIdx))
    (hcoreCost : CoreCostBounded ParamConfig.default M r coreCost)
    (hsp_core : C_sp_core ≤ C_sp) (hsp_rt : C_sp_rt ≤ C_sp)
    (hCore : MeetsContract w p coreAdapterIdx (coreAdapterContract M r coreCost C_core C_sp_core w))
    (hRoute : MeetsContract w p routeIdx (routeOrCutContract C_rt C_sp_rt w)) :
    p.procs[base]? = some (outerDecompMainProc (outerMainIndicesOf base)) ∧
    MeetsContract w p (outerMainIndicesOf base).bParams (computeParamsContract ParamConfig.default w) ∧
    MeetsContract w p (outerMainIndicesOf base).bStripIso (stripIsolatedContract w) ∧
    RecSubprocs M r w p (outerRecIndicesOf base) C_core C_rt C_sp 80 := by
  set pre13 : List Stmt :=
    [ outerDecompMainProc (outerMainIndicesOf base)
    , computeParamsProc ParamConfig.default
    , coreLevelProc
    , stripIsolatedProc
    , restrictProc
    , setDiffProc
    , outerContractEdgesProc
    , outerRoundPortCutProc
    , padToBisectionProc
    , buildInjPairProc
    , fakeCompletionProc
    , outerGameProc (outerGameIndicesOf base coreAdapterIdx routeIdx)
    , outerDecompRecProc (outerRecIndicesOf base)
    ]
  set cLen := (compLabelsInProcs (base + 16)).length
  have hHas' : p.HasAt base (pre13 ++ removeFakeProcs (base + 13) ++
      compLabelsInProcs (base + 16) ++ portGraphProcs (base + 16 + cLen)) := hHas
  have hpre_at : ∀ off < 13, (pre13 ++ removeFakeProcs (base + 13) ++
      compLabelsInProcs (base + 16) ++ portGraphProcs (base + 16 + cLen))[off]? = pre13[off]? := fun off hoff => by
    have h1 : off < pre13.length := by simp [pre13]; omega
    simp only [List.append_assoc, List.getElem?_append_left h1]
  have hp0 : p.procs[base]? = some (outerDecompMainProc (outerMainIndicesOf base)) := by
    simpa using hasAt_single_outer hHas' (off := 0) (by rw [hpre_at 0 (by decide)]; rfl)
  have hp1 : p.HasAt (base + 1) [computeParamsProc ParamConfig.default] :=
    hasAt_singleton_outer hHas' (off := 1) (by rw [hpre_at 1 (by decide)]; rfl)
  have hp2 : p.HasAt (base + 2) [coreLevelProc] :=
    hasAt_singleton_outer hHas' (off := 2) (by rw [hpre_at 2 (by decide)]; rfl)
  have hp3 : p.HasAt (base + 3) [stripIsolatedProc] :=
    hasAt_singleton_outer hHas' (off := 3) (by rw [hpre_at 3 (by decide)]; rfl)
  have hp4 : p.HasAt (base + 4) [restrictProc] :=
    hasAt_singleton_outer hHas' (off := 4) (by rw [hpre_at 4 (by decide)]; rfl)
  have hp5 : p.HasAt (base + 5) [setDiffProc] :=
    hasAt_singleton_outer hHas' (off := 5) (by rw [hpre_at 5 (by decide)]; rfl)
  have hp6 : p.HasAt (base + 6) [outerContractEdgesProc] :=
    hasAt_singleton_outer hHas' (off := 6) (by rw [hpre_at 6 (by decide)]; rfl)
  have hp7 : p.HasAt (base + 7) [outerRoundPortCutProc] :=
    hasAt_singleton_outer hHas' (off := 7) (by rw [hpre_at 7 (by decide)]; rfl)
  have hp8 : p.HasAt (base + 8) [padToBisectionProc] :=
    hasAt_singleton_outer hHas' (off := 8) (by rw [hpre_at 8 (by decide)]; rfl)
  have hp9 : p.HasAt (base + 9) [buildInjPairProc] :=
    hasAt_singleton_outer hHas' (off := 9) (by rw [hpre_at 9 (by decide)]; rfl)
  have hp10 : p.HasAt (base + 10) [fakeCompletionProc] :=
    hasAt_singleton_outer hHas' (off := 10) (by rw [hpre_at 10 (by decide)]; rfl)
  have hp11 : p.HasAt (base + 11) [outerGameProc (outerGameIndicesOf base coreAdapterIdx routeIdx)] :=
    hasAt_singleton_outer hHas' (off := 11) (by rw [hpre_at 11 (by decide)]; rfl)
  have hp12 : p.procs[base + 12]? = some (outerDecompRecProc (outerRecIndicesOf base)) :=
    hasAt_single_outer hHas' (off := 12) (by rw [hpre_at 12 (by decide)]; rfl)
  have hHasRF : p.HasAt (base + 13) (removeFakeProcs (base + 13)) :=
    hasAt_slice_outer hHas' (off := 13) fun i hi => by
      have hpre_len : pre13.length = 13 := rfl
      simp only [List.append_assoc]
      rw [List.getElem?_append_right (by omega : pre13.length ≤ 13 + i)]
      have hsub : 13 + i - pre13.length = i := by omega
      rw [hsub, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  have hHasComp : p.HasAt (base + 16) (compLabelsInProcs (base + 16)) :=
    hasAt_slice_outer hHas' (off := 16) fun i hi => by
      have hpre_len : (pre13 ++ removeFakeProcs (base + 13)).length = 16 := by
        simp [pre13, removeFakeProcs]
      simp only [List.append_assoc]
      rw [← List.append_assoc pre13 (removeFakeProcs (base + 13)),
          List.getElem?_append_right (by omega : (pre13 ++ removeFakeProcs (base + 13)).length ≤ 16 + i)]
      have hsub : 16 + i - (pre13 ++ removeFakeProcs (base + 13)).length = i := by omega
      rw [hsub, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  have hHasPort : p.HasAt (base + 16 + cLen) (portGraphProcs (base + 16 + cLen)) := by
    have h1 : p.HasAt (base + (16 + cLen)) (portGraphProcs (base + 16 + cLen)) :=
      hasAt_slice_outer hHas' (off := 16 + cLen) fun i hi => by
        have hpre_len : (pre13 ++ removeFakeProcs (base + 13) ++ compLabelsInProcs (base + 16)).length = 16 + cLen := by
          simp only [List.length_append, cLen]
          have h13 : pre13.length = 13 := rfl
          have h3 : (removeFakeProcs (base + 13)).length = 3 := by simp [removeFakeProcs]
          omega
        rw [List.getElem?_append_right (by omega)]
        have hsub : 16 + cLen + i - (pre13 ++ removeFakeProcs (base + 13) ++ compLabelsInProcs (base + 16)).length = i := by
          omega
        rw [hsub, List.getElem?_eq_getElem hi]
    rwa [← Nat.add_assoc] at h1
  have hGameSub : OuterGameSubprocs M r w p (outerGameIndicesOf base coreAdapterIdx routeIdx)
      coreCost routeOrCut routerCallCost C_core C_rt C_sp_core C_sp_rt C_sp 80 :=
    { hcoreCost := hcoreCost
      hroute := routeOrCut_isMatchingPlayer_callCost
      hrouteC := fun G' X' pairs Δ L b z' hX hloop hΔ hdeg hL hcard hb hvalid =>
        routerCallCost_bounded G' X' pairs Δ L b z' hX hloop hΔ hdeg hL hcard hb hvalid
      hsp_core := hsp_core
      hsp_rt := hsp_rt
      hCoreLevel := coreLevelProc_spec hp2
      hCoreProg := hCore
      hRouteProg := hRoute
      hPad := padToBisectionProc_spec hp8
      hInj := buildInjPairProc_spec hp9
      hFake := fakeCompletionProc_spec hp10 }
  refine ⟨hp0, computeParamsProc_spec hp1, stripIsolatedProc_spec hp3, ?_⟩
  exact
    { hSelf := hp12
      hComp := compLabelsIn_spec hHasComp
      hPort := portGraph_spec hHasPort
      hGame := outerGameProc_spec hp11 hGameSub
      hRound := outerRoundPortCutProc_spec hp7
      hRestrict := restrictProc_spec hp4
      hStripIso := stripIsolatedProc_spec hp3
      hContract := outerContractEdgesProc_spec hp6
      hRF := removeFake_spec_prog hHasRF
      hSetDiff := setDiffProc_spec hp5 }


end MinCostFlow.ExpanderDecomp
