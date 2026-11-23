module

public import MinCostFlow.SparseCore.Program.CompAsmWrapDefs
import Mathlib.Tactic

/-!
# Space, Word-Size, and Cost Bounds for the P4 Wrapper (`CompAsmWrapBounds`)

Proves the input-independent polynomial space bounds, word-size dominance, and polylogarithmic
cost bounds (`bundleLogFactor M N ^ 3` at init, `bundleLogFactor M N` at batch and export) needed
to assemble `AsmCompFamilySpec` and `AsmCompFamilyAt` from `compAsmProcs` (`CompAsmWrapDefs.lean`):

* `compAsmInitSpacePoly`: degree-`6` `PolyBound` dominating `2 + L + dynGraphSize vCap eCap +
  compInitSpace` (and implying `canonWordBits < w` directly from
  `h + initSpace.eval (vCap + eCap + L + k) < 2 ^ w`).
* `compAsmBatchSpacePoly`: quadratic `PolyBound` dominating `1 + words + compBatchSpaceFull`.
* `compAsmExportSpacePoly`: quadratic `PolyBound` dominating `compExportSpace`.
* `compAsmSpec`: concrete `AsmCompFamilySpec` with `wordExp capExp = max 7 (2 * capExp)`
  (hence `wordExp 3 = 7 ≤ 39`).
* `compAsmInitCost_le`, `compAsmBatchCost_le`, `compAsmExportCost_le`: exact polylog cost bounds
  for all three operations.
-/

@[expose] public noncomputable section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## 1. Elementary log and `canonLw` bounds -/

lemma real_log_le_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have h := Real.log_le_sub_one_of_pos hx
  linarith

lemma real_log_nat_add_two_le_log2 (n : ℕ) :
    Real.log ((n : ℝ) + 2) ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := by
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) (n + 2)
  have hlt_r : ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (Nat.log 2 (n + 2) + 1) := by exact_mod_cast hlt.le
  have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 (n + 2) + 1)) :=
    Real.log_le_log (by positivity) hlt_r
  rw [Real.log_pow] at h1
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hd_nn : (0 : ℝ) ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := by positivity
  calc Real.log ((n : ℝ) + 2)
      ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) * Real.log 2 := h1
    _ ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 hd_nn
    _ = ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := mul_one _

lemma canonLw_le_linear {K_AN : ℝ} {L n k : ℕ}
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65) :
    canonLw K_AN L n k ≤ L + k + 6 * n + 100 := by
  unfold canonLw
  have h1 : Nat.log 2 (k + 1) ≤ k + 1 := Nat.log_le_self 2 (k + 1)
  have h2 : Nat.log 2 (n + 2) ≤ n + 2 := Nat.log_le_self 2 (n + 2)
  have h3 : Nat.log 2 (Nat.log 2 (n + 2) + 2) ≤ Nat.log 2 (n + 2) + 2 := Nat.log_le_self 2 _
  omega

lemma canonLw_le_readout2_of_rho {K_AN : ℝ} {L_in n0 k_nat M N capExp : ℕ}
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    (hn : n0 ≤ N) (hk : k_nat ≤ (M + N + 2) ^ capExp) :
    canonLw K_AN L_in n0 k_nat ≤
      L_in + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) := by
  set B := M + N + 2
  set d := Nat.log 2 B + 1
  have hB2 : 2 ≤ B := by omega
  have hd1 : 1 ≤ d := by omega
  have hB_lt : B < 2 ^ d := Nat.lt_pow_succ_log_self (by decide) B
  have hk_log : Nat.log 2 (k_nat + 1) ≤ capExp * d + 1 := by
    have hpow_le : B ^ capExp ≤ (2 ^ d) ^ capExp := Nat.pow_le_pow_left hB_lt.le capExp
    have hpow_pos : 1 ≤ (2 ^ d) ^ capExp := Nat.one_le_pow _ _ (by positivity)
    have h1 : k_nat + 1 < 2 ^ (capExp * d + 2) := by
      have h3 : (2 ^ d) ^ capExp = 2 ^ (capExp * d) := by rw [← pow_mul, mul_comm]
      have h4 : 2 ^ (capExp * d + 2) = 4 * 2 ^ (capExp * d) := by rw [pow_succ, pow_succ]; ring
      omega
    have hlt := Nat.log_lt_of_lt_pow (by omega) h1
    omega
  have hn_log : Nat.log 2 (Nat.log 2 (n0 + 2) + 2) ≤ d := by
    have hle1 : Nat.log 2 (n0 + 2) ≤ Nat.log 2 B := Nat.log_mono_right (by omega)
    have hlog_le_self : Nat.log 2 B ≤ B := Nat.log_le_self 2 B
    have hlt2 : Nat.log 2 (n0 + 2) + 2 < 2 ^ (d + 1) := by
      have h4 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
      omega
    have hlt := Nat.log_lt_of_lt_pow (by omega) hlt2
    omega
  unfold canonLw sparseCoreReadout2LimbConst
  have hmul : (capExp + 128) * d = capExp * d + 128 * d := Nat.add_mul capExp 128 d
  omega

/-! ## 2. Spec definitions (`compAsmSpec`) -/

/-- Coefficient of the degree-`6` polynomial init-space bound for `compAsmInitProc`. -/
def compAsmInitSpaceCoeff (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) : ℕ :=
  let c := max c_AN 1
  let K := Nat.ceil (max K_AN 1)
  let S := WideWord.simScale Q_AN
  30000000 * (S + 1) * (K + 1) * (c + 1) ^ 2

/-- Input-independent polynomial init-space bound (`deg = 6`). -/
def compAsmInitSpacePoly (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) : PolyBound :=
  { coeff := compAsmInitSpaceCoeff Q_AN c_AN K_AN, deg := 6 }

/-- Input-independent polynomial batch-space bound (`deg = 2`). -/
def compAsmBatchSpacePoly : PolyBound := { coeff := 50, deg := 2 }

/-- Input-independent polynomial export-space bound (`deg = 2`). -/
def compAsmExportSpacePoly : PolyBound := { coeff := 250, deg := 2 }

/-- Input-independent cost multiplier `mul capExp limbMul` covering init (`bundleLogFactor^3`),
batch (`bundleLogFactor`), and export (`bundleLogFactor`). -/
def compAsmMul (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (capExp limbMul : ℕ) : ℕ :=
  let c := max c_AN 1
  let K := Nat.ceil (max K_AN 1)
  let S := WideWord.simScale Q_AN
  let R := (lemma55Module Q_AN c_AN K_AN 4).regBound
  let Cw := limbMul + capExp + 130
  let Cls := 4 * c * (limbMul + 10)
  let Cov := Cls ^ 2 + S * Cls ^ 2 * (K * (4 * Cls + 8) + 1) + Cw ^ 2 + 2
  let Cl55 := lsfInitCostFactor * (Cov + 1) + 2002000 * (limbMul + 1) * Cw ^ 2 + 20000
  4 * (2 * R + 10) * Cl55 + 250000 * (Cw + 1) + 20000

/-- Concrete `AsmCompFamilySpec` for the P4 wrapper (`wordExp 3 = 7 ≤ 39`). -/
def compAsmSpec (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) : AsmCompFamilySpec where
  mul capExp limbMul := compAsmMul Q_AN c_AN K_AN capExp limbMul
  rootCost _ := 200
  wordExp capExp := max 7 (2 * capExp)
  initSpace _ := compAsmInitSpacePoly Q_AN c_AN K_AN
  batchSpace _ := compAsmBatchSpacePoly
  exportSpace _ := compAsmExportSpacePoly

theorem compAsmSpec_wordExp_le_39 (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) :
    (compAsmSpec Q_AN c_AN K_AN).wordExp 3 ≤ 39 := by
  unfold compAsmSpec; dsimp only; decide

/-! ## 3. Polynomial space bounds -/

private lemma mwuEdgeStepSpace_le_poly {L L_w P_fp X : ℕ}
    (hL : L ≤ X) (hP : P_fp ≤ 4 * L) (hLw : L_w ≤ 100 * X) (hX2 : 2 ≤ X) :
    mwuEdgeStepSpace L L_w P_fp ≤ 2000000 * X ^ 3 := by
  unfold mwuEdgeStepSpace fixedDivideSpace positiveExponentialSpace expHornerSpace
    roundedSquaringSpace integerDivideSpace unsignedDivideSpace
  have hsq : L_w * L_w ≤ 10000 * X ^ 2 := by nlinarith
  have hcu : (P_fp + 4) * (L_w * L_w) ≤ 60000 * X ^ 3 := by
    have : P_fp + 4 ≤ 6 * X := by omega
    nlinarith
  have hX2_le : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hX_le : X ≤ X ^ 2 := by nlinarith
  nlinarith

private lemma lsfStaticSize_le_poly {vCap eCap n0 L_w X : ℕ}
    (hX2 : 2 ≤ X) (hv : vCap ≤ X) (he : eCap ≤ X) (hn : n0 ≤ X) (hLw : L_w ≤ 100 * X) :
    lsfStaticSize vCap eCap n0 n0 L_w ≤ 500 * X ^ 2 := by
  unfold lsfStaticSize lsfHdrSize tBlockSize tHdrSize fECap fAncSize fAncHdrSize
    wBlockSize wHdrSize auxSize auxHdrSize auxLogCap hldDepthBound dynGraphSize
  have h1 : Nat.log 2 (n0 + 1) ≤ X + 1 := le_trans (Nat.log_le_self 2 _) (by omega)
  have h2 : Nat.log 2 n0 ≤ X := le_trans (Nat.log_le_self 2 _) hn
  have h3 : n0 * (Nat.log 2 (n0 + 1) + 1) ≤ 3 * X ^ 2 := by nlinarith
  have h4 : (Nat.log 2 n0 + 1) * (Nat.log 2 n0 + 2) ≤ 6 * X ^ 2 := by nlinarith
  have h5 : eCap * L_w ≤ 100 * X ^ 2 := by nlinarith
  have hX_le : X ≤ X ^ 2 := by nlinarith
  have h1_le : 1 ≤ X ^ 2 := by nlinarith
  omega

set_option maxHeartbeats 600000 in
private lemma lsstSpace_le_poly {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {n0 m0 L X : ℕ}
    (hX2 : 2 ≤ X) (hn : n0 ≤ X) (hm : m0 ≤ X) (hL : L ≤ X) :
    let c := max c_AN 1
    let K := Nat.ceil (max K_AN 1)
    let S := WideWord.simScale Q_AN
    let L_sim := WideWord.lsstLSimMin c_AN n0 (2 * m0) L 4
    L_sim ≤ 40 * c * X ∧
    WideWord.lsstSpace Q_AN K_AN n0 (2 * m0) L_sim 4 ≤
      4000000 * (S + 1) * (K + 1) * (c + 1) ^ 2 * X ^ 4 := by
  intro c K S L_sim
  have hc1 : 1 ≤ c := le_max_right _ _
  have hc_ge : c_AN ≤ c := le_max_left _ _
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; have := Nat.le_ceil (max K_AN 1); dsimp only [K] at h0; rw [h0, Nat.cast_zero] at this
    linarith [le_max_right K_AN 1])
  have hkw : WideWord.kWidthOf (2 * m0) L ≤ 7 * X := by
    unfold WideWord.kWidthOf
    have hlog2 : Nat.log 2 (4 * (2 * m0) + 2) ≤ 4 * X := by
      have h1 : 4 * (2 * m0) + 2 < 2 ^ (4 * X) := by
        have h2X : 8 * X + 2 < 2 ^ (4 * X) := by
          clear * - hX2
          induction X with
          | zero => omega
          | succ t ih =>
            rcases t with _ | _ | t
            · omega
            · decide
            · have hih := ih (by omega)
              have h16 : 2 ^ 4 = 16 := by decide
              have h4e : 4 * (t + 1 + 1 + 1) = 4 * (t + 1 + 1) + 4 := by omega
              rw [h4e, pow_add, h16]; omega
        omega
      exact (Nat.log_lt_of_lt_pow (by omega) h1).le
    omega
  have hw' : WideWord.w'Max c_AN n0 (2 * m0) L 4 ≤ 40 * c * X := by
    unfold WideWord.w'Max
    have hlog : Nat.log 2 (6 + 16 * (2 * m0)) ≤ 6 * X := by
      have h1 : 6 + 16 * (2 * m0) < 2 ^ (6 * X) := by
        have h2X : 6 + 32 * X < 2 ^ (6 * X) := by
          clear * - hX2
          induction X with
          | zero => omega
          | succ t ih =>
            rcases t with _ | _ | t
            · omega
            · decide
            · have hih := ih (by omega)
              have h64 : 2 ^ 6 = 64 := by decide
              have h6e : 6 * (t + 1 + 1 + 1) = 6 * (t + 1 + 1) + 6 := by omega
              rw [h6e, pow_add, h64]; omega
        omega
      exact (Nat.log_lt_of_lt_pow (by omega) h1).le
    calc c_AN * (Nat.log 2 (6 + 16 * (2 * m0)) + WideWord.kWidthOf (2 * m0) L * 4 + 3)
        ≤ c * (6 * X + 7 * X * 4 + 3) := Nat.mul_le_mul hc_ge (by omega)
      _ ≤ c * (40 * X) := Nat.mul_le_mul_left c (by omega)
      _ = 40 * c * X := by ring
  have hLsim : L_sim ≤ 40 * c * X := max_le (le_trans hkw (by nlinarith)) hw'
  refine ⟨hLsim, ?_⟩
  have han : WideWord.anCostBound K_AN n0 (2 * m0) L_sim 4 ≤ 4000 * K * c * X ^ 3 := by
    unfold WideWord.anCostBound
    have hK_r : max K_AN 0 ≤ (K : ℝ) :=
      le_trans (max_le (le_max_left K_AN 1) (by norm_num : (0 : ℝ) ≤ max K_AN 1)) (Nat.le_ceil _)
    have hlogn : Real.log ((n0 : ℝ) + 2) ≤ (X : ℝ) + 2 := by
      have := real_log_le_self_of_pos (by positivity : (0 : ℝ) < (n0 : ℝ) + 2)
      have hn_r : (n0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hn
      linarith
    have hlogn_nn : 0 ≤ Real.log ((n0 : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ n0 by positivity])
    have hll : Cited.logLogFactor n0 ≤ ((X : ℝ) + 2) ^ 2 := by
      unfold Cited.logLogFactor
      have hpos : (0 : ℝ) < Real.log ((n0 : ℝ) + 2) :=
        Real.log_pos (by linarith [show (0 : ℝ) ≤ n0 by positivity])
      have h2 := real_log_le_self_of_pos hpos
      nlinarith
    have hwf : Cited.weightFactor n0 (2 ^ (L_sim * 4)) ≤ ((X : ℝ) + 2) * (4 * (L_sim : ℝ) + 5) := by
      unfold Cited.weightFactor
      have hpow_le : (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) ≤ (2 : ℝ) ^ (L_sim * 4 + 2) := by
        have : 2 ^ (L_sim * 4) + 2 ≤ 2 ^ (L_sim * 4 + 2) := by
          rw [pow_add]; have : 1 ≤ 2 ^ (L_sim * 4) := Nat.one_le_pow _ _ (by decide); omega
        exact_mod_cast this
      have h1 : Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) ≤ ((L_sim * 4 + 2 : ℕ) : ℝ) := by
        have hlt := Real.log_le_log (by positivity) hpow_le
        rw [Real.log_pow] at hlt
        have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hnn : (0 : ℝ) ≤ ((L_sim * 4 + 2 : ℕ) : ℝ) := by positivity
        calc Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2)
            ≤ ((L_sim * 4 + 2 : ℕ) : ℝ) * Real.log 2 := hlt
          _ ≤ ((L_sim * 4 + 2 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 hnn
          _ = ((L_sim * 4 + 2 : ℕ) : ℝ) := mul_one _
      have h2 : Real.log (Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) + 2) ≤ 4 * (L_sim : ℝ) + 5 := by
        have hnn : 0 ≤ Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) :=
          Real.log_nonneg (by linarith [show (0 : ℝ) ≤ ((2 ^ (L_sim * 4) : ℕ) : ℝ) by positivity])
        have hle := real_log_le_self_of_pos (by linarith : (0 : ℝ) < Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) + 2)
        have h1' : Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) ≤ 4 * (L_sim : ℝ) + 2 := by
          have hr : ((L_sim * 4 + 2 : ℕ) : ℝ) = 4 * (L_sim : ℝ) + 2 := by push_cast; ring
          exact hr ▸ h1
        linarith
      exact (mul_le_mul_of_nonneg_left h2 hlogn_nn).trans (mul_le_mul_of_nonneg_right hlogn (by positivity))
    have hX_r : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    have hm_r : (m0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hm
    have hc_r : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hLsim_r : (L_sim : ℝ) ≤ 40 * (c : ℝ) * (X : ℝ) := by exact_mod_cast hLsim
    have hK_nn : (0 : ℝ) ≤ (K : ℝ) := by positivity
    have hsum_bd : Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_sim * 4)) ≤
        360 * (c : ℝ) * (X : ℝ) ^ 2 := by
      have h1 : ((X : ℝ) + 2) ^ 2 ≤ 4 * (X : ℝ) ^ 2 := by nlinarith
      have h2 : 4 * (L_sim : ℝ) + 5 ≤ 170 * (c : ℝ) * (X : ℝ) := by nlinarith
      have h3 : ((X : ℝ) + 2) * (4 * (L_sim : ℝ) + 5) ≤ (2 * (X : ℝ)) * (170 * (c : ℝ) * (X : ℝ)) := by
        have hnn : 0 ≤ 4 * (L_sim : ℝ) + 5 := by positivity
        nlinarith
      nlinarith
    have hprod_bd : max K_AN 0 * ((4 * (2 * m0) : ℕ) + 1 : ℝ) *
        (Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_sim * 4))) ≤
        ((4000 * K * c * X ^ 3 : ℕ) : ℝ) := by
      have h4m : ((4 * (2 * m0) : ℕ) + 1 : ℝ) ≤ 9 * (X : ℝ) := by push_cast; linarith
      have hnn1 : 0 ≤ Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_sim * 4)) :=
        logLog_add_weightFactor_nonneg n0 _ (by
          have : 1 ≤ L_sim := le_trans (by unfold WideWord.kWidthOf; omega) (le_max_left _ _)
          exact le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega)))
      have hstep1 : max K_AN 0 * ((4 * (2 * m0) : ℕ) + 1 : ℝ) ≤ (K : ℝ) * (9 * (X : ℝ)) :=
        mul_le_mul hK_r h4m (by positivity) hK_nn
      have hstep2 := mul_le_mul hstep1 hsum_bd hnn1 (by positivity)
      push_cast at hstep2 ⊢
      have h3240 : (K : ℝ) * (9 * (X : ℝ)) * (360 * (c : ℝ) * (X : ℝ) ^ 2) =
          3240 * ((K : ℝ) * (c : ℝ) * (X : ℝ) ^ 3) := by ring
      have h4000 : (4000 : ℝ) * (K : ℝ) * (c : ℝ) * (X : ℝ) ^ 3 =
          4000 * ((K : ℝ) * (c : ℝ) * (X : ℝ) ^ 3) := by ring
      have hnn3 : (0 : ℝ) ≤ (K : ℝ) * (c : ℝ) * (X : ℝ) ^ 3 := by positivity
      linarith
    exact Nat.ceil_le.mpr hprod_bd
  -- Bound `weightsSpace`, `simDecodeSpace`, and total `lsstSpace`
  set M := (S + 1) * (K + 1) * (c + 1) ^ 2
  have hX1 : 1 ≤ X := by omega
  have hX_2 : X ≤ X ^ 2 := by nlinarith
  have hX2_3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hX3_4 : X ^ 3 ≤ X ^ 4 := by nlinarith
  have hLsim_sq : L_sim * L_sim ≤ 1600 * c ^ 2 * X ^ 2 := by nlinarith
  have hwt : WideWord.weightsSpace (2 * m0) L_sim ≤ 200000 * c ^ 2 * X ^ 3 := by
    unfold WideWord.weightsSpace integerDivideSpace unsignedDivideSpace
    have h1 : 2 * m0 ≤ 2 * X := by omega
    have h13 : 13 * L_sim ≤ 520 * c * X := by nlinarith
    have hc2 : c ≤ c ^ 2 := by nlinarith
    have h2' : 18 * L_sim + 2 * (3 * (2 * L_sim) + 2 + 5 * (2 * L_sim) * (2 * L_sim + 1) + 3 * (2 * L_sim)) =
        40 * (L_sim * L_sim) + 62 * L_sim + 4 := by ring
    rw [h2']
    have h3' : 40 * (L_sim * L_sim) + 62 * L_sim + 4 ≤ 70000 * c ^ 2 * X ^ 2 := by nlinarith
    have h4' : 2 * m0 * (40 * (L_sim * L_sim) + 62 * L_sim + 4) ≤ 2 * X * (70000 * c ^ 2 * X ^ 2) :=
      Nat.mul_le_mul h1 h3'
    nlinarith
  have hsim : WideWord.simDecodeSpace Q_AN (2 * (2 * m0)) (4 * (2 * m0)) L_sim 4
      (WideWord.anCostBound K_AN n0 (2 * m0) L_sim 4) ≤ 3000000 * M * X ^ 4 := by
    unfold WideWord.simDecodeSpace
    set encLen := 2 + 3 * (4 * (2 * m0))
    have henc : encLen ≤ 25 * X := by dsimp [encLen]; omega
    have h16 : 2 ^ 4 = 16 := by decide
    rw [h16]
    have hterm1 : (1 + 2 * (2 * m0)) * L_sim ≤ 200 * c * X ^ 2 := by
      have : 1 + 2 * (2 * m0) ≤ 5 * X := by omega
      nlinarith
    have hterm2 : encLen * (L_sim * 16 + L_sim) ≤ 17000 * c * X ^ 2 := by
      have : L_sim * 16 + L_sim ≤ 680 * c * X := by linarith
      nlinarith
    have hterm3 : S * L_sim * 16 * (WideWord.anCostBound K_AN n0 (2 * m0) L_sim 4 + encLen + 1) ≤
        2600000 * M * X ^ 4 := by
      have hA : S * L_sim * 16 ≤ 640 * (S + 1) * c * X := by
        have : S ≤ S + 1 := Nat.le_succ S
        have h1 := Nat.mul_le_mul this hLsim
        nlinarith
      have hB : WideWord.anCostBound K_AN n0 (2 * m0) L_sim 4 + encLen + 1 ≤
          4026 * (K + 1) * c * X ^ 3 := by
        have h1 : K ≤ K + 1 := Nat.le_succ K
        have h2 : 4000 * K * c * X ^ 3 ≤ 4000 * (K + 1) * c * X ^ 3 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1))
        have h3 : 25 * X + 1 ≤ 26 * (K + 1) * c * X ^ 3 := by
          have : 1 ≤ (K + 1) * c := Nat.mul_pos (by omega) hc1
          nlinarith
        linarith
      have hprod := Nat.mul_le_mul hA hB
      have heq : 640 * (S + 1) * c * X * (4026 * (K + 1) * c * X ^ 3) =
          2576640 * ((S + 1) * (K + 1) * c ^ 2) * X ^ 4 := by ring
      have hc_le : c ^ 2 ≤ (c + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ c) 2
      have hM_ge : (S + 1) * (K + 1) * c ^ 2 ≤ M :=
        Nat.mul_le_mul_left _ hc_le
      nlinarith
    have hc_M : c ≤ M := by
      have hsk : 1 ≤ (S + 1) * (K + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      have hcc : c ≤ (c + 1) ^ 2 := by nlinarith
      dsimp only [M]; exact le_trans hcc (Nat.le_mul_of_pos_left _ hsk)
    have h1M : 1 ≤ M := by dsimp only [M]; exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by positivity)
    have h1 : 200 * c * X ^ 2 ≤ 200 * M * X ^ 4 := by
      have := Nat.mul_le_mul hc_M (hX2_3.trans hX3_4)
      have heq : 200 * (c * X ^ 2) = 200 * c * X ^ 2 := by ring
      have heq2 : 200 * (M * X ^ 4) = 200 * M * X ^ 4 := by ring
      linarith [Nat.mul_le_mul_left 200 this]
    have h2 : 17000 * c * X ^ 2 ≤ 17000 * M * X ^ 4 := by
      have := Nat.mul_le_mul hc_M (hX2_3.trans hX3_4)
      have heq : 17000 * (c * X ^ 2) = 17000 * c * X ^ 2 := by ring
      have heq2 : 17000 * (M * X ^ 4) = 17000 * M * X ^ 4 := by ring
      linarith [Nat.mul_le_mul_left 17000 this]
    have h3 : 1 ≤ M * X ^ 4 := Nat.mul_pos h1M (Nat.pow_pos (by omega : 0 < X))
    have hLsim_M : L_sim ≤ 40 * (M * X ^ 4) := by
      have hX_4 : X ≤ X ^ 4 := hX_2.trans (hX2_3.trans hX3_4)
      have := Nat.mul_le_mul hc_M hX_4
      have h40 := Nat.mul_le_mul_left 40 this
      have heq : 40 * (c * X) = 40 * c * X := by ring
      linarith
    have hM1 : 200 * M * X ^ 4 = 200 * (M * X ^ 4) := Nat.mul_assoc _ _ _
    have hM2 : 17000 * M * X ^ 4 = 17000 * (M * X ^ 4) := Nat.mul_assoc _ _ _
    have hM3 : 2600000 * M * X ^ 4 = 2600000 * (M * X ^ 4) := Nat.mul_assoc _ _ _
    have hM4 : 3000000 * M * X ^ 4 = 3000000 * (M * X ^ 4) := Nat.mul_assoc _ _ _
    dsimp only
    linarith
  have hc2_M : c ^ 2 ≤ M := by
    have hsk : 1 ≤ (S + 1) * (K + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    have hcc : c ^ 2 ≤ (c + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ c) 2
    dsimp only [M]; exact le_trans hcc (Nat.le_mul_of_pos_left _ hsk)
  have hc_M : c ≤ M := le_trans (by nlinarith) hc2_M
  have h1M : 1 ≤ M := by dsimp only [M]; exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by positivity)
  unfold WideWord.lsstSpace
  have hrest1 : 2 * m0 * L_sim ≤ 80 * c * X ^ 2 := by
    have h1 := Nat.mul_le_mul (show 2 * m0 ≤ 2 * X by omega) hLsim
    have heq : 2 * X * (40 * c * X) = 80 * c * X ^ 2 := by ring
    omega
  have hrest2 : (2 + 3 * (4 * (2 * m0))) * L_sim ≤ 1000 * c * X ^ 2 := by
    have h1 := Nat.mul_le_mul (show 2 + 3 * (4 * (2 * m0)) ≤ 25 * X by omega) hLsim
    have heq : 25 * X * (40 * c * X) = 1000 * c * X ^ 2 := by ring
    omega
  have hw_M : 200000 * c ^ 2 * X ^ 3 ≤ 200000 * M * X ^ 4 := by
    have := Nat.mul_le_mul hc2_M hX3_4
    have heq : 200000 * (c ^ 2 * X ^ 3) = 200000 * c ^ 2 * X ^ 3 := by ring
    have heq2 : 200000 * (M * X ^ 4) = 200000 * M * X ^ 4 := by ring
    linarith [Nat.mul_le_mul_left 200000 this]
  have hr_M : 1080 * c * X ^ 2 ≤ 1080 * M * X ^ 4 := by
    have := Nat.mul_le_mul hc_M (hX2_3.trans hX3_4)
    have heq : 1080 * (c * X ^ 2) = 1080 * c * X ^ 2 := by ring
    have heq2 : 1080 * (M * X ^ 4) = 1080 * M * X ^ 4 := by ring
    linarith [Nat.mul_le_mul_left 1080 this]
  have h1_M : 1 ≤ M * X ^ 4 := Nat.mul_pos h1M (Nat.pow_pos (by omega : 0 < X))
  have hX_M : X ≤ M * X ^ 4 := le_trans (hX_2.trans (hX2_3.trans hX3_4)) (Nat.le_mul_of_pos_left _ h1M)
  have hM1 : 3000000 * M * X ^ 4 = 3000000 * (M * X ^ 4) := Nat.mul_assoc _ _ _
  have hM2 : 200000 * M * X ^ 4 = 200000 * (M * X ^ 4) := Nat.mul_assoc _ _ _
  have hM3 : 1080 * M * X ^ 4 = 1080 * (M * X ^ 4) := Nat.mul_assoc _ _ _
  have hM4 : 4000000 * (S + 1) * (K + 1) * (c + 1) ^ 2 * X ^ 4 = 4000000 * (M * X ^ 4) := by
    dsimp only [M]; simp only [Nat.mul_assoc]
  rw [hM4]
  linarith

lemma canonLw_mono_n (K_AN : ℝ) (L k : ℕ) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    canonLw K_AN L n₁ k ≤ canonLw K_AN L n₂ k := by
  unfold canonLw
  have h1 : Nat.log 2 (Nat.log 2 (n₁ + 2) + 2) ≤ Nat.log 2 (Nat.log 2 (n₂ + 2) + 2) :=
    Nat.log_mono_right (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 2)
  omega

private lemma compAsmCompSpace_le {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {vCap eCap' L P_fp k L_w nC mC X : ℕ}
    (hX2 : 2 ≤ X) (hv : vCap ≤ X) (he : eCap' ≤ X) (hL : L ≤ X) (hk : k ≤ X)
    (hn : nC ≤ X) (hm : mC ≤ X) (hP : P_fp ≤ 4 * L)
    (hLw : L_w ≤ 100 * X) (hLwC : canonLw K_AN L nC k ≤ 100 * X) :
    dynGraphSize vCap eCap' +
      canonWinSpace Q_AN K_AN c_AN 4 L P_fp k L_w vCap eCap' nC mC ≤
      25000000 * ((WideWord.simScale Q_AN + 1) * (Nat.ceil (max K_AN 1) + 1) *
        (max c_AN 1 + 1) ^ 2) * X ^ 5 := by
  set c := max c_AN 1
  set K := Nat.ceil (max K_AN 1)
  set S := WideWord.simScale Q_AN
  set M := (S + 1) * (K + 1) * (c + 1) ^ 2
  have hX_2 : X ≤ X ^ 2 := by nlinarith
  have hX2_3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hX3_4 : X ^ 3 ≤ X ^ 4 := by nlinarith
  have hX4_5 : X ^ 4 ≤ X ^ 5 := by nlinarith
  have h1M : 1 ≤ M := by
    dsimp only [M]; exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by positivity)
  have hc1 : 1 ≤ c := le_max_right _ _
  have hc_M : c ≤ M := by
    have hsk : 1 ≤ (S + 1) * (K + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    have hcc : c ≤ (c + 1) ^ 2 := by nlinarith
    dsimp only [M]; exact le_trans hcc (Nat.le_mul_of_pos_left _ hsk)
  obtain ⟨hLsim0, hlsst0⟩ := lsstSpace_le_poly (Q_AN := Q_AN) (c_AN := c_AN) (K_AN := K_AN)
    (n0 := nC) (m0 := mC) (L := L) hX2 hn hm hL
  have hLsim : WideWord.lsstLSimMin c_AN nC (2 * mC) L 4 ≤ 40 * c * X := hLsim0
  have hlsst : WideWord.lsstSpace Q_AN K_AN nC (2 * mC) (WideWord.lsstLSimMin c_AN nC (2 * mC) L 4) 4 ≤
      4000000 * M * X ^ 4 := by
    simpa only [M, S, K, c, Nat.mul_assoc] using hlsst0
  have hstC := lsfStaticSize_le_poly hX2 (vCap := vCap) (eCap := eCap') (n0 := nC) (L_w := canonLw K_AN L nC k)
    hv he hn hLwC
  have hstH := lsfStaticSize_le_poly hX2 (vCap := vCap) (eCap := eCap') (n0 := nC) (L_w := L_w)
    hv he hn hLw
  have hmwu := mwuEdgeStepSpace_le_poly (L := L) (L_w := canonLw K_AN L nC k) (P_fp := P_fp)
    hL hP hLwC hX2
  have hX2_M4 : X ^ 2 ≤ M * X ^ 4 := le_trans (hX2_3.trans hX3_4) (Nat.le_mul_of_pos_left _ h1M)
  have hX3_M5 : X ^ 3 ≤ M * X ^ 5 := le_trans (hX3_4.trans hX4_5) (Nat.le_mul_of_pos_left _ h1M)
  have h1_M4 : 1 ≤ M * X ^ 4 := Nat.mul_pos h1M (Nat.pow_pos (by omega : 0 < X))
  have haux_term : 200 * (nC + mC + 1) * (canonLw K_AN L nC k +
      WideWord.lsstLSimMin c_AN nC (2 * mC) L 4 + auxLogCap nC + 20) + 1000 ≤
      200000 * M * X ^ 4 := by
    have ha1 : auxLogCap nC ≤ 2 * X := by unfold auxLogCap; have := Nat.log_le_self 2 (nC + 1); omega
    have h1 : nC + mC + 1 ≤ 3 * X := by omega
    have hXc : X ≤ c * X := Nat.le_mul_of_pos_left X hc1
    have hLsim' : WideWord.lsstLSimMin c_AN nC (2 * mC) L 4 ≤ 40 * (c * X) := by
      simpa only [Nat.mul_assoc] using hLsim
    have h2 : canonLw K_AN L nC k + WideWord.lsstLSimMin c_AN nC (2 * mC) L 4 + auxLogCap nC + 20 ≤
        160 * (c * X) := by omega
    have h3 : 200 * (nC + mC + 1) * (canonLw K_AN L nC k + WideWord.lsstLSimMin c_AN nC (2 * mC) L 4 +
        auxLogCap nC + 20) ≤ 200 * (3 * X) * (160 * (c * X)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 200 h1) h2
    have h4 : 200 * (3 * X) * (160 * (c * X)) = 96000 * (c * X ^ 2) := by ring
    have h5 : c * X ^ 2 ≤ M * X ^ 4 := Nat.mul_le_mul hc_M (hX2_3.trans hX3_4)
    have h6 : 96000 * (c * X ^ 2) ≤ 96000 * (M * X ^ 4) := Nat.mul_le_mul_left _ h5
    have h7 : 200000 * M * X ^ 4 = 200000 * (M * X ^ 4) := by ring
    linarith
  have hl55 : lemma55Space Q_AN K_AN c_AN 4 L (canonLw K_AN L nC k) P_fp k vCap eCap' nC mC ≤
      8000000 * M * X ^ 5 := by
    unfold lemma55Space
    dsimp only
    have hlsfSp : lsfStaticSize vCap eCap' nC nC (canonLw K_AN L nC k) + 2 * (eCap' * canonLw K_AN L nC k) +
        WideWord.lsstSpace Q_AN K_AN nC (2 * mC) (WideWord.lsstLSimMin c_AN nC (2 * mC) L 4) 4 +
        200 * (nC + mC + 1) * (canonLw K_AN L nC k + WideWord.lsstLSimMin c_AN nC (2 * mC) L 4 +
          auxLogCap nC + 20) + 1000 ≤ 5000000 * M * X ^ 4 := by
      have heLw : eCap' * canonLw K_AN L nC k ≤ 100 * X ^ 2 := by
        have h1 := Nat.mul_le_mul he hLwC
        have heq : X * (100 * X) = 100 * X ^ 2 := by ring
        omega
      have hM4 : 4000000 * M * X ^ 4 = 4000000 * (M * X ^ 4) := by ring
      have hM4b : 200000 * M * X ^ 4 = 200000 * (M * X ^ 4) := by ring
      have hM4c : 5000000 * M * X ^ 4 = 5000000 * (M * X ^ 4) := by ring
      linarith
    have hkSp : k * (lsfStaticSize vCap eCap' nC nC (canonLw K_AN L nC k) + 2 * (eCap' * canonLw K_AN L nC k) +
        WideWord.lsstSpace Q_AN K_AN nC (2 * mC) (WideWord.lsstLSimMin c_AN nC (2 * mC) L 4) 4 +
        200 * (nC + mC + 1) * (canonLw K_AN L nC k + WideWord.lsstLSimMin c_AN nC (2 * mC) L 4 +
          auxLogCap nC + 20) + 1000) ≤ 5000000 * M * X ^ 5 := by
      have h2 := Nat.mul_le_mul hk hlsfSp
      have heq : X * (5000000 * M * X ^ 4) = 5000000 * M * X ^ 5 := by ring
      linarith
    have heL : eCap' * L ≤ X ^ 2 := by
      have := Nat.mul_le_mul he hL; rwa [← sq] at this
    have hmax : max (4 * canonLw K_AN L nC k) (mwuEdgeStepSpace L (canonLw K_AN L nC k) P_fp) ≤
        2000000 * X ^ 3 := max_le (by linarith) hmwu
    have hM5 : 5000000 * M * X ^ 5 = 5000000 * (M * X ^ 5) := by ring
    have hM5b : 8000000 * M * X ^ 5 = 8000000 * (M * X ^ 5) := by ring
    have hX_M5 : X ≤ M * X ^ 5 := (hX_2.trans hX2_3).trans hX3_M5
    have hX2_M5 : X ^ 2 ≤ M * X ^ 5 := hX2_3.trans hX3_M5
    linarith
  have hwb : canonWinWordBound Q_AN c_AN K_AN 4 L P_fp k vCap eCap' nC mC ≤
      9000000 * M * X ^ 5 := by
    unfold canonWinWordBound
    dsimp only
    have hdg : dynGraphSize vCap eCap' ≤ 20 * X := by unfold dynGraphSize; omega
    have heL : eCap' * L ≤ X ^ 2 := by
      have := Nat.mul_le_mul he hL; rwa [← sq] at this
    have hhld : 3 * (4 * k * (hldDepthBound nC + 1)) ≤ 100 * X ^ 3 := by
      unfold hldDepthBound
      have h1 : Nat.log 2 nC ≤ X := le_trans (Nat.log_le_self 2 _) hn
      have h2 : (Nat.log 2 nC + 1) * (Nat.log 2 nC + 2) ≤ (2 * X) * (2 * X) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : (2 * X) * (2 * X) = 4 * X ^ 2 := by ring
      have h4 : k * ((Nat.log 2 nC + 1) * (Nat.log 2 nC + 2) + 1) ≤ X * (5 * X ^ 2) :=
        Nat.mul_le_mul hk (by linarith)
      have h5 : X * (5 * X ^ 2) = 5 * X ^ 3 := by ring
      linarith
    have h2P : 2 * P_fp + 9 ≤ 20 * X := by omega
    have hmax1 : max (2 * P_fp + 9) (3 * (4 * k * (hldDepthBound nC + 1))) ≤ 100 * X ^ 3 :=
      max_le (by linarith) hhld
    have hX_M5 : X ≤ M * X ^ 5 := (hX_2.trans hX2_3).trans hX3_M5
    have hX2_M5 : X ^ 2 ≤ M * X ^ 5 := hX2_3.trans hX3_M5
    have hM5a : 8000000 * M * X ^ 5 = 8000000 * (M * X ^ 5) := by ring
    have hM5b : 8500000 * M * X ^ 5 = 8500000 * (M * X ^ 5) := by ring
    have hM5c : 9000000 * M * X ^ 5 = 9000000 * (M * X ^ 5) := by ring
    have hleft : dynGraphSize vCap eCap' + eCap' * L + k +
        lemma55Space Q_AN K_AN c_AN 4 L (canonLw K_AN L nC k) P_fp k vCap eCap' nC mC ≤
        8500000 * M * X ^ 5 := by linarith
    have hmax2 := max_le hleft (le_trans hmax1 (by linarith))
    linarith
  have h2pow : 2 ^ canonWinWordBits Q_AN c_AN K_AN 4 L P_fp k vCap eCap' nC mC ≤
      16384 + 18000000 * M * X ^ 5 := by
    unfold canonWinWordBits
    rcases max_choice (3 * 4 + 2)
        (Nat.log 2 (canonWinWordBound Q_AN c_AN K_AN 4 L P_fp k vCap eCap' nC mC) + 1) with hEq | hEq
    · rw [hEq, show 2 ^ (3 * 4 + 2) = 16384 by decide]; exact Nat.le_add_right _ _
    · rw [hEq]
      have hlt : 2 ^ (Nat.log 2 (canonWinWordBound Q_AN c_AN K_AN 4 L P_fp k vCap eCap' nC mC) + 1) ≤
          2 * canonWinWordBound Q_AN c_AN K_AN 4 L P_fp k vCap eCap' nC mC := by
        rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by unfold canonWinWordBound; exact Nat.succ_ne_zero _))
      have h18 : 2 * (9000000 * M * X ^ 5) = 18000000 * M * X ^ 5 := by ring
      linarith
  unfold canonWinSpace
  dsimp only
  have hdg' : dynGraphSize vCap eCap' ≤ 20 * X := by unfold dynGraphSize; omega
  have hHnd : dynGraphSize vCap eCap' + eCap' * L + max nC mC + 1 ≤ 30 * X ^ 2 := by
    have : eCap' * L ≤ X ^ 2 := by
      have := Nat.mul_le_mul he hL; rwa [← sq] at this
    have : max nC mC ≤ X := max_le hn hm
    linarith
  have h1_M5 : 1 ≤ M * X ^ 5 := Nat.mul_pos h1M (Nat.pow_pos (by omega : 0 < X))
  have hX2_M5 : X ^ 2 ≤ M * X ^ 5 := hX2_3.trans hX3_M5
  have hM5a : 18000000 * M * X ^ 5 = 18000000 * (M * X ^ 5) := by ring
  have hM5c : 19000000 * M * X ^ 5 = 19000000 * (M * X ^ 5) := by ring
  have hmax_s : max (2 ^ canonWinWordBits Q_AN c_AN K_AN 4 L P_fp k vCap eCap' nC mC)
      (dynGraphSize vCap eCap' + eCap' * L + max nC mC + 1) ≤
      19000000 * M * X ^ 5 := max_le (by linarith) (by linarith)
  have hk_st : k * lsfStaticSize vCap eCap' nC nC L_w ≤ 500 * X ^ 3 := by
    have h1 := Nat.mul_le_mul hk hstH
    have h2 : X * (500 * X ^ 2) = 500 * X ^ 3 := by ring
    linarith
  have hM5d : 25000000 * M * X ^ 5 = 25000000 * (M * X ^ 5) := by ring
  have hX_M5 : X ≤ M * X ^ 5 := (hX_2.trans hX2_3).trans hX3_M5
  linarith

set_option maxHeartbeats 400000 in
/-- Total `init` space (wrapper overhead + `gCopy` + `compInitSpace`) is bounded by
`(compAsmInitSpacePoly Q_AN c_AN K_AN).eval (vCap + eCap + L + k)`. Also bounds
`2 ^ canonWordBits` for every edgeful component `C` by the same polynomial. -/
theorem compAsmInitSpace_le {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {vCap eCap L P_fp k : ℕ} {G : MGraph}
    (hP : P_fp ≤ 4 * L) (hG_val : G.IsValid)
    (hGn : G.n ≤ vCap) (hGm : G.m ≤ eCap)
    (g0Ptr lenArr bComp : ℕ) :
    let W := canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L P_fp
    let L_w := if G.m = 0 then 1 else canonLw K_AN L G.n k
    let eCap' := max eCap 1
    2 + L + dynGraphSize vCap eCap +
      compInitSpace W k G [g0Ptr, lenArr, L, P_fp, k, L_w, vCap, eCap', bComp] ≤
      (compAsmInitSpacePoly Q_AN c_AN K_AN).eval (vCap + eCap + L + k) := by
  intro W L_w eCap'
  set X := vCap + eCap + L + k + 2
  set c := max c_AN 1
  set K := Nat.ceil (max K_AN 1)
  set S := WideWord.simScale Q_AN
  set M := (S + 1) * (K + 1) * (c + 1) ^ 2
  have hX2 : 2 ≤ X := by omega
  have hX_2 : X ≤ X ^ 2 := by nlinarith
  have hX2_3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hX3_4 : X ^ 3 ≤ X ^ 4 := by nlinarith
  have hX4_5 : X ^ 4 ≤ X ^ 5 := by nlinarith
  have hX5_6 : X ^ 5 ≤ X ^ 6 := by nlinarith
  have h1M : 1 ≤ M := by dsimp only [M]; exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by positivity)
  have heCap'_le : eCap' ≤ X := by dsimp only [eCap', X]; omega
  have hLw_canon : canonLw K_AN L G.n k ≤ 100 * X := by
    have := canonLw_le_linear (L := L) (n := G.n) (k := k) hRho
    omega
  have hLw_le : L_w ≤ 100 * X := by
    dsimp only [L_w]; split_ifs <;> omega
  have hcomp_bd : ∀ C ∈ edgefulComps G,
      dynGraphSize vCap eCap' +
        canonWinSpace Q_AN K_AN c_AN 4 L P_fp k L_w vCap eCap'
          (compGraph G C).n (compGraph G C).m ≤
        25000000 * M * X ^ 5 := by
    intro C hC
    have hC_mem : C ∈ components G := (Finset.mem_filter.mp hC).1
    have hnC : (compGraph G C).n ≤ G.n := compGraph_n_le hC_mem
    have hmC : (compGraph G C).m ≤ G.m := by
      change (compEdgeSet G C).card ≤ G.E.card
      exact Finset.card_le_card (Finset.filter_subset _ _)
    exact compAsmCompSpace_le hX2 (by omega) heCap'_le (by omega) (by omega) (by omega) (by omega)
      hP hLw_le (le_trans (canonLw_mono_n K_AN L k hnC) hLw_canon)
  -- Sum over `edgefulComps G` (at most `G.m ≤ eCap ≤ X` components)
  have hcard : (edgefulComps G).card ≤ G.m := by
    have hsum1 : (edgefulComps G).card ≤ (edgefulComps G).sum (fun C => (compGraph G C).m) := by
      calc (edgefulComps G).card = (edgefulComps G).sum (fun _ => 1) := by simp
        _ ≤ (edgefulComps G).sum (fun C => (compGraph G C).m) :=
            Finset.sum_le_sum fun C hC => (Finset.mem_filter.mp hC).2
    have hsum_le : (edgefulComps G).sum (fun C => (compGraph G C).m) ≤ G.m := by
      have hsub := Finset.sum_le_sum_of_subset (f := fun C => (compGraph G C).m)
        (show edgefulComps G ⊆ components G from Finset.filter_subset _ _)
      have htot := components_sum_m G hG_val
      omega
    exact hsum1.trans hsum_le
  have hsum_bd : (edgefulComps G).sum (fun C =>
      dynGraphSize vCap eCap' + W.winSpace k L_w vCap eCap' (compGraph G C).n (compGraph G C).m) ≤
      25000000 * M * X ^ 6 := by
    calc (edgefulComps G).sum (fun C =>
          dynGraphSize vCap eCap' + W.winSpace k L_w vCap eCap' (compGraph G C).n (compGraph G C).m)
        ≤ (edgefulComps G).sum (fun _ => 25000000 * M * X ^ 5) :=
          Finset.sum_le_sum fun C hC => hcomp_bd C hC
      _ = (edgefulComps G).card * (25000000 * M * X ^ 5) := by simp
      _ ≤ X * (25000000 * M * X ^ 5) := Nat.mul_le_mul_right _ (by omega)
      _ = 25000000 * M * X ^ 6 := by rw [mul_left_comm, ← pow_succ']
  -- Combine with static terms
  have hbase : 2 + L + dynGraphSize vCap eCap + compStaticSize vCap eCap' L_w + G.m * k +
      vCap + G.n + 3 * G.m ≤ 5000 * X ^ 2 := by
    unfold dynGraphSize compStaticSize compHdrSize
    have hmk : G.m * k ≤ X ^ 2 := by
      have := Nat.mul_le_mul (show G.m ≤ X by omega) (show k ≤ X by omega); rwa [← sq] at this
    omega
  have hgoal : (compAsmInitSpacePoly Q_AN c_AN K_AN).eval (vCap + eCap + L + k) =
      30000000 * M * X ^ 6 := by
    unfold compAsmInitSpacePoly compAsmInitSpaceCoeff PolyBound.eval
    dsimp only [M, S, K, c, X]
    simp only [Nat.mul_assoc]
  rw [hgoal]
  have hci : compInitSpace W k G [g0Ptr, lenArr, L, P_fp, k, L_w, vCap, eCap', bComp] =
      compStaticSize vCap eCap' L_w + G.m * k + vCap + G.n + 3 * G.m +
        (edgefulComps G).sum (fun C => dynGraphSize vCap eCap' +
          W.winSpace k L_w vCap eCap' (compGraph G C).n (compGraph G C).m) := rfl
  rw [hci]
  have hX2_M6 : X ^ 2 ≤ M * X ^ 6 :=
    le_trans (hX2_3.trans (hX3_4.trans (hX4_5.trans hX5_6))) (Nat.le_mul_of_pos_left _ h1M)
  have hM6a : 25000000 * M * X ^ 6 = 25000000 * (M * X ^ 6) := Nat.mul_assoc _ _ _
  have hM6b : 30000000 * M * X ^ 6 = 30000000 * (M * X ^ 6) := Nat.mul_assoc _ _ _
  have hbase_le : 2 + L + dynGraphSize vCap eCap +
      (compStaticSize vCap eCap' L_w + G.m * k + vCap + G.n + 3 * G.m) ≤ 5000 * (M * X ^ 6) :=
    le_trans (by omega) (Nat.mul_le_mul_left 5000 hX2_M6)
  have htot_le : 2 + L + dynGraphSize vCap eCap +
      (compStaticSize vCap eCap' L_w + G.m * k + vCap + G.n + 3 * G.m +
        (edgefulComps G).sum (fun C => dynGraphSize vCap eCap' +
          W.winSpace k L_w vCap eCap' (compGraph G C).n (compGraph G C).m)) ≤
      5000 * (M * X ^ 6) + 25000000 * (M * X ^ 6) := by
    rw [← Nat.add_assoc]
    exact Nat.add_le_add hbase_le (hsum_bd.trans_eq hM6a)
  rw [hM6b]
  have hcoef : 5000 * (M * X ^ 6) + 25000000 * (M * X ^ 6) ≤ 30000000 * (M * X ^ 6) := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by decide)
  exact htot_le.trans hcoef

/-- `canonWordBits < w` follows directly from `h + initSpace.eval (vCap + eCap + L + k) < 2 ^ w`! -/
theorem canonWordBits_le_of_initSpace {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {w vCap eCap L P_fp k h : ℕ} {G : MGraph} {C : Finset ℕ}
    (hP : P_fp ≤ 4 * L) (hG_val : G.IsValid)
    (hGn : G.n ≤ vCap) (hGm : G.m ≤ eCap)
    (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap)
    (hC : C ∈ edgefulComps G)
    (hsp : h + (compAsmInitSpacePoly Q_AN c_AN K_AN).eval (vCap + eCap + L + k) < 2 ^ w) :
    canonWordBits Q_AN c_AN K_AN 4 L P_fp (compGraph G C) k ≤ w := by
  set W := canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L P_fp
  set L_w := if G.m = 0 then 1 else canonLw K_AN L G.n k
  set eCap' := max eCap 1
  have htot := compAsmInitSpace_le (k := k) hQ hRho hP hG_val hGn hGm 0 0 0
  dsimp only at htot
  have hC_mem : C ∈ components G := (Finset.mem_filter.mp hC).1
  have hv_le : canonVCap (compGraph G C) ≤ vCap := by
    unfold canonVCap
    have hsub : C ⊆ G.V := fun v hv => by
      rw [← components_biUnion_V G]; exact Finset.mem_biUnion.mpr ⟨C, hC_mem, hv⟩
    have hsup : C.sup id < vCap := by
      have hne : C.Nonempty := by
        obtain ⟨e, he⟩ := Finset.card_pos.mp (Finset.mem_filter.mp hC).2
        exact ⟨G.tail e, (Finset.mem_filter.mp he).2⟩
      exact (Finset.sup_lt_iff (by obtain ⟨v, hv⟩ := hne; exact lt_of_le_of_lt (Nat.zero_le _) (hVlt v (hsub hv)))).mpr
        fun v hv => hVlt v (hsub hv)
    change C.sup id + 1 ≤ vCap; omega
  have he_le : canonECap (compGraph G C) ≤ eCap' := by
    unfold canonECap
    have hsub : compEdgeSet G C ⊆ G.E := Finset.filter_subset _ _
    have he1 : 1 ≤ eCap' := le_max_right _ _
    have hsup : (compEdgeSet G C).sup id < eCap' :=
      (Finset.sup_lt_iff he1).mpr fun e he => lt_of_lt_of_le (hElt e (hsub he)) (le_max_left _ _)
    change (compEdgeSet G C).sup id + 1 ≤ eCap'; omega
  have hwin_le := lsfWindowSpace_le_canonWinSpace (Q_AN := Q_AN) (K_AN := K_AN) (c_AN := c_AN)
    (h := 4) (L_in := L) (L_w := L_w) (P_fp := P_fp) (k_nat := k) hv_le he_le
  have h2pow_le_win : 2 ^ canonWordBits Q_AN c_AN K_AN 4 L P_fp (compGraph G C) k ≤
      W.winSpace k L_w vCap eCap' (compGraph G C).n (compGraph G C).m := by
    have h1 : 2 ^ canonWordBits Q_AN c_AN K_AN 4 L P_fp (compGraph G C) k ≤
        lsfWindowSpace Q_AN K_AN c_AN 4 L L_w P_fp k vCap eCap' (compGraph G C) := by
      unfold lsfWindowSpace
      exact le_trans (le_max_left _ _) (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))
    exact h1.trans hwin_le
  have hmem_le_sum : W.winSpace k L_w vCap eCap' (compGraph G C).n (compGraph G C).m ≤
      (edgefulComps G).sum (fun C' => dynGraphSize vCap eCap' +
        W.winSpace k L_w vCap eCap' (compGraph G C').n (compGraph G C').m) :=
    le_trans (Nat.le_add_left _ _)
      (Finset.single_le_sum
        (f := fun C' => dynGraphSize vCap eCap' +
          W.winSpace k L_w vCap eCap' (compGraph G C').n (compGraph G C').m)
        (fun _ _ => Nat.zero_le _) hC)
  have h2pow_lt : 2 ^ canonWordBits Q_AN c_AN K_AN 4 L P_fp (compGraph G C) k < 2 ^ w := by
    have hci : (edgefulComps G).sum (fun C' => dynGraphSize vCap eCap' +
        W.winSpace k L_w vCap eCap' (compGraph G C').n (compGraph G C').m) ≤
        compInitSpace W k G [0, 0, L, P_fp, k, L_w, vCap, eCap', 0] := by
      simp only [compInitSpace, List.getD_cons_zero, List.getD_cons_succ]; omega
    have htot' : 2 + L + dynGraphSize vCap eCap +
        compInitSpace W k G [0, 0, L, P_fp, k, L_w, vCap, eCap', 0] ≤
        (compAsmInitSpacePoly Q_AN c_AN K_AN).eval (vCap + eCap + L + k) := htot
    omega
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2pow_lt |>.le

/-- Batch space bound: `1 + words + compBatchSpaceFull ≤ compAsmBatchSpacePoly.eval (vCap + eCap + L + k + words)`. -/
theorem compAsmBatchSpace_le {vCap eCap L k words numU : ℕ}
    (hnumU : numU ≤ words) :
    1 + words + (11 + 3 * numU + words + 2 * max eCap 1 + 8 * vCap + k * (8 + 12 * vCap)) ≤
      compAsmBatchSpacePoly.eval (vCap + eCap + L + k + words) := by
  unfold compAsmBatchSpacePoly PolyBound.eval
  dsimp only
  set X := vCap + eCap + L + k + words + 2
  have hkv : k * vCap ≤ X ^ 2 := by
    have := Nat.mul_le_mul (show k ≤ X by omega) (show vCap ≤ X by omega); rwa [← sq] at this
  have hX : X ≤ X ^ 2 := by
    have := Nat.mul_le_mul (show 1 ≤ X by omega) (le_refl X); simpa [sq] using this
  have he : max eCap 1 ≤ eCap + 1 := by omega
  have hmul : k * (8 + 12 * vCap) = 8 * k + 12 * (k * vCap) := by ring
  omega

/-- Export space bound: `compExportSpace ≤ compAsmExportSpacePoly.eval (M + N + k + vCap + eCap + L)`. -/
theorem compAsmExportSpace_le {K_AN : ℝ} {M N k vCap eCap L n0 : ℕ}
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65) (hn0 : n0 ≤ vCap) :
    16 + 2 * vCap + 6 * max eCap 1 + 2 * max eCap 1 * canonLw K_AN L n0 k ≤
      compAsmExportSpacePoly.eval (M + N + k + vCap + eCap + L) := by
  unfold compAsmExportSpacePoly PolyBound.eval
  dsimp only
  set X := M + N + k + vCap + eCap + L + 2
  have hLw := canonLw_le_linear (L := L) (n := n0) (k := k) hRho
  have hLwX : canonLw K_AN L n0 k ≤ 100 * X := by omega
  have he : max eCap 1 ≤ X := by omega
  have hmul : 2 * max eCap 1 * canonLw K_AN L n0 k ≤ 200 * X ^ 2 := by
    have h1 := Nat.mul_le_mul he hLwX
    have h2 : 2 * max eCap 1 * canonLw K_AN L n0 k = 2 * (max eCap 1 * canonLw K_AN L n0 k) :=
      Nat.mul_assoc 2 _ _
    have heq : X * (100 * X) = 100 * X ^ 2 := by ring
    omega
  have hX : X ≤ X ^ 2 := by
    have := Nat.mul_le_mul (show 1 ≤ X by omega) (le_refl X); simpa [sq] using this
  omega

end MinCostFlow.SparseCore.Program
