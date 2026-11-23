module

public import MinCostFlow.SparseCore.Program.CompAsmWrapSpace
import Mathlib.Tactic

/-!
# Polylogarithmic Cost Bounds for the P4 Wrapper (`CompAsmWrapCost`)

Proves the polylogarithmic machine cost bounds for `compAsmInitProc` (`bundleLogFactor M N ^ 3`),
`compAsmBatchProc` (`bundleLogFactor M N`), and `compAsmExportProc` (`bundleLogFactor M N`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.Num


private lemma mwuEdgeStepCost_le_log6 {L L_w P_fp limbMul Cw D : ℕ}
    (hD : 1 ≤ D) (hL_Lw : L ≤ L_w) (hL : L ≤ limbMul * D ^ 2) (hP : P_fp ≤ 4 * L)
    (hLw : L_w ≤ Cw * D ^ 2) (hCw1 : 1 ≤ Cw) :
    mwuEdgeStepCost L L_w P_fp ≤ 2000000 * (limbMul + 1) * Cw ^ 2 * D ^ 6 := by
  set Z := (limbMul + 1) * Cw ^ 2 * D ^ 6
  have h1D2 : 1 ≤ D ^ 2 := Nat.one_le_pow 2 D hD
  have h1D4 : 1 ≤ D ^ 4 := Nat.one_le_pow 4 D hD
  have hD2_4 : D ^ 2 ≤ D ^ 4 := by nlinarith
  have hD4_6 : D ^ 4 ≤ D ^ 6 := by nlinarith
  have hCw_sq : Cw ≤ Cw ^ 2 := by nlinarith
  have h1Z : 1 ≤ Z := by
    dsimp only [Z]
    exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos hCw1)) (Nat.pow_pos hD)
  have hLw_Z : L_w ≤ Z := by
    have : Cw * D ^ 2 ≤ (limbMul + 1) * Cw ^ 2 * D ^ 6 := by
      have h1 : Cw * D ^ 2 ≤ Cw ^ 2 * D ^ 6 := Nat.mul_le_mul hCw_sq (hD2_4.trans hD4_6)
      rw [Nat.mul_assoc]
      exact h1.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    exact hLw.trans this
  have hLw2_le : L_w * L_w ≤ Cw ^ 2 * D ^ 4 := by
    have h1 := Nat.mul_le_mul hLw hLw
    have heq : Cw * D ^ 2 * (Cw * D ^ 2) = Cw ^ 2 * D ^ 4 := by ring
    omega
  have hLw2_Z : L_w * L_w ≤ Z := by
    have : Cw ^ 2 * D ^ 4 ≤ (limbMul + 1) * Cw ^ 2 * D ^ 6 := by
      have h1 : Cw ^ 2 * D ^ 4 ≤ Cw ^ 2 * D ^ 6 := Nat.mul_le_mul_left _ hD4_6
      rw [Nat.mul_assoc]
      exact h1.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    exact hLw2_le.trans this
  have hP4 : P_fp + 4 ≤ 4 * (limbMul + 1) * D ^ 2 := by nlinarith
  have hP4_Z : P_fp + 4 ≤ 4 * Z := by
    have : (limbMul + 1) * D ^ 2 ≤ Z := by
      dsimp only [Z]
      have h1 : 1 ≤ Cw ^ 2 := Nat.one_le_pow 2 Cw hCw1
      have h2 : D ^ 2 ≤ Cw ^ 2 * D ^ 6 := (hD2_4.trans hD4_6).trans (Nat.le_mul_of_pos_left _ h1)
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left (limbMul + 1) h2
    linarith
  have hPLw2 : (P_fp + 4) * (L_w * L_w) ≤ 4 * Z := by
    have h1 := Nat.mul_le_mul hP4 hLw2_le
    have heq : 4 * (limbMul + 1) * D ^ 2 * (Cw ^ 2 * D ^ 4) = 4 * Z := by dsimp only [Z]; ring
    omega
  have hPLw : (P_fp + 4) * L_w ≤ 4 * Z := by
    have h1 := Nat.mul_le_mul hP4 hLw
    have h2 : (limbMul + 1) * Cw * D ^ 4 ≤ Z := by
      dsimp only [Z]
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hCw_sq) hD4_6
    have heq : 4 * (limbMul + 1) * D ^ 2 * (Cw * D ^ 2) = 4 * ((limbMul + 1) * Cw * D ^ 4) := by ring
    omega
  have hL2_Z : L * L ≤ Z := (Nat.mul_le_mul hL_Lw hL_Lw).trans hLw2_Z
  have hL_Z : L ≤ Z := hL_Lw.trans hLw_Z
  have hsp : mwuEdgeStepSpace L L_w P_fp ≤ 1000 * Z := by
    unfold mwuEdgeStepSpace fixedDivideSpace positiveExponentialSpace expHornerSpace
      roundedSquaringSpace integerDivideSpace unsignedDivideSpace
    have heq : 2 * (10 * L_w + (3 * (3 * L_w) + 2 + 5 * (3 * L_w) * (3 * L_w + 1) + 3 * (3 * L_w))) +
        (2 * L_w + 1 + ((P_fp + 4) * (13 * L_w + (3 * L_w + 2 + 5 * L_w * (L_w + 1) + 3 * L_w) + 1) + L_w) +
          ((1 + 2) * (11 * L_w + 1) + L_w)) +
        (11 * L + 1) =
        5 * ((P_fp + 4) * (L_w * L_w)) + 24 * ((P_fp + 4) * L_w) + 3 * (P_fp + 4) +
        90 * (L_w * L_w) + 123 * L_w + 11 * L + 9 := by ring
    rw [heq]; omega
  have hexp : positiveExponentialCost L_w P_fp 1 ≤ 25000 * Z := by
    unfold positiveExponentialCost
    simp only [sq]
    have hexpand : (P_fp + 4) * (500 * (L_w * L_w) + 2000 * L_w + 2000) +
        (1 + 2) * (200 * (L_w * L_w) + 500 * L_w + 500) + 100 * L_w + 1000 =
        500 * ((P_fp + 4) * (L_w * L_w)) + 2000 * ((P_fp + 4) * L_w) + 2000 * (P_fp + 4) +
        600 * (L_w * L_w) + 1600 * L_w + 2500 := by ring
    rw [hexpand]; omega
  unfold mwuEdgeStepCost
  have heq : 2 * (3 * L_w * (900 * L_w + 644) + 900 * L_w + 700) +
      (2 * L * (38 * (2 * L) + 35) + 269 * L + 248) =
      5400 * (L_w * L_w) + 5664 * L_w + 152 * (L * L) + 339 * L + 1648 := by ring
  have hZ2m : 2000000 * (limbMul + 1) * Cw ^ 2 * D ^ 6 = 2000000 * Z := by dsimp only [Z]; ring
  omega

private lemma weightFactor_le_log2 {nC L_sim Cls D : ℕ}
    (hD1 : 1 ≤ D) (hlogn : Real.log ((nC : ℝ) + 2) ≤ (D : ℝ))
    (hLsim : L_sim ≤ Cls * D ^ 2) :
    Cited.weightFactor nC (2 ^ (L_sim * 4)) ≤ ((4 * Cls + 7 : ℕ) : ℝ) * (D : ℝ) ^ 2 := by
  unfold Cited.weightFactor
  have h1D2 : 1 ≤ D ^ 2 := Nat.one_le_pow 2 D hD1
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
  have harg : Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) + 2 ≤
      ((4 * Cls + 4 : ℕ) : ℝ) * (D : ℝ) ^ 2 := by
    have hLsim_r : (L_sim : ℝ) ≤ (Cls : ℝ) * (D : ℝ) ^ 2 := by exact_mod_cast hLsim
    have h1D2_r : (1 : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast h1D2
    have h1' : ((L_sim * 4 + 2 : ℕ) : ℝ) = (L_sim : ℝ) * 4 + 2 := by push_cast; ring
    have h4' : ((4 * Cls + 4 : ℕ) : ℝ) * (D : ℝ) ^ 2 =
        4 * ((Cls : ℝ) * (D : ℝ) ^ 2) + 4 * (D : ℝ) ^ 2 := by push_cast; ring
    linarith
  have hlog_w_nn : 0 ≤ Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ ((2 ^ (L_sim * 4) : ℕ) : ℝ) by positivity])
  have harg_pos : (0 : ℝ) < Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) + 2 := by linarith
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hlog_arg : Real.log (Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) + 2) ≤
      ((4 * Cls + 7 : ℕ) : ℝ) * (D : ℝ) := by
    have hle := Real.log_le_log harg_pos harg
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hle
    have ha1 := real_log_le_self_of_pos (by positivity : (0 : ℝ) < ((4 * Cls + 4 : ℕ) : ℝ))
    have ha2 := real_log_le_self_of_pos hD_pos
    have hD1_r : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    have h4le : ((4 * Cls + 4 : ℕ) : ℝ) ≤ ((4 * Cls + 4 : ℕ) : ℝ) * (D : ℝ) :=
      le_mul_of_one_le_right (by positivity) hD1_r
    have h7eq : ((4 * Cls + 7 : ℕ) : ℝ) * (D : ℝ) =
        ((4 * Cls + 4 : ℕ) : ℝ) * (D : ℝ) + 3 * (D : ℝ) := by push_cast; ring
    have h2cast : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2cast] at hle
    linarith
  calc Real.log ((nC : ℝ) + 2) * Real.log (Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) + 2)
      ≤ (D : ℝ) * (((4 * Cls + 7 : ℕ) : ℝ) * (D : ℝ)) := by
        have hnn1 : 0 ≤ Real.log (Real.log (((2 ^ (L_sim * 4) : ℕ) : ℝ) + 2) + 2) :=
          Real.log_nonneg (by linarith)
        exact mul_le_mul hlogn hlog_arg hnn1 (by positivity)
    _ = ((4 * Cls + 7 : ℕ) : ℝ) * (D : ℝ) ^ 2 := by ring

private lemma lsfOverhead_le_log6 {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {nC mC L k M N capExp limbMul : ℕ}
    (hn : nC ≤ N) (hm : mC ≤ M) (hk : k ≤ (M + N + 2) ^ capExp)
    (hL : L ≤ limbMul * bundleLogFactor M N) :
    let c := max c_AN 1
    let K := Nat.ceil (max K_AN 1)
    let S := WideWord.simScale Q_AN
    let Cw := limbMul + capExp + 130
    let Cls := 4 * c * (limbMul + 10)
    let Cov : ℕ := Cls ^ 2 + S * Cls ^ 2 * (K * (4 * Cls + 8) + 1) + Cw ^ 2 + 2
    lsfOverhead Q_AN c_AN K_AN nC mC L (canonLw K_AN L nC k) 4 ≤
      (Cov : ℝ) * ((bundleLogFactor M N ^ 3 : ℕ) : ℝ) := by
  intro c K S Cw Cls Cov
  set B := M + N + 2
  set D := Nat.log 2 B + 1
  have hD1 : 1 ≤ D := by omega
  have hD_le_D2 : D ≤ D ^ 2 := by nlinarith
  have h1D2 : 1 ≤ D ^ 2 := Nat.one_le_pow 2 D hD1
  have hB_lt : B < 2 ^ D := Nat.lt_pow_succ_log_self (by decide) B
  have hc1 : 1 ≤ c := le_max_right _ _
  have hc_ge : c_AN ≤ c := le_max_left _ _
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; have := Nat.le_ceil (max K_AN 1); dsimp only [K] at h0; rw [h0, Nat.cast_zero] at this
    linarith [le_max_right K_AN 1])
  have hblg : bundleLogFactor M N = D ^ 2 := rfl
  have hblg3 : bundleLogFactor M N ^ 3 = D ^ 6 := by rw [hblg, ← pow_mul]
  have hLw : canonLw K_AN L nC k ≤ Cw * D ^ 2 := by
    have h1 := canonLw_le_readout2_of_rho (L_in := L) (n0 := nC) (k_nat := k)
      (M := M) (N := N) (capExp := capExp) hRho hn hk
    unfold sparseCoreReadout2LimbConst at h1
    change canonLw K_AN L nC k ≤ L + (capExp + 128) * D at h1
    rw [hblg] at hL
    have h2 : (capExp + 128) * D ≤ (capExp + 130) * D ^ 2 := Nat.mul_le_mul (by omega) hD_le_D2
    have h3 : L + (capExp + 130) * D ^ 2 ≤ Cw * D ^ 2 := by
      dsimp only [Cw]
      have heq : (limbMul + capExp + 130) * D ^ 2 = limbMul * D ^ 2 + (capExp + 130) * D ^ 2 := by ring
      omega
    omega
  have hkw : WideWord.kWidthOf (2 * mC) L ≤ (limbMul + 7) * D ^ 2 := by
    unfold WideWord.kWidthOf
    have hlt : 4 * (2 * mC) + 2 < 2 ^ (D + 3) := by
      have h8 : 2 ^ (D + 3) = 8 * 2 ^ D := by rw [pow_add]; ring
      omega
    have hlog : Nat.log 2 (4 * (2 * mC) + 2) ≤ D + 2 := by
      have := Nat.log_lt_of_lt_pow (by omega) hlt; omega
    rw [hblg] at hL; nlinarith
  have hw' : WideWord.w'Max c_AN nC (2 * mC) L 4 ≤ Cls * D ^ 2 := by
    unfold WideWord.w'Max
    have hlt : 6 + 16 * (2 * mC) < 2 ^ (D + 5) := by
      have h32 : 2 ^ (D + 5) = 32 * 2 ^ D := by rw [pow_add]; ring
      omega
    have hlog : Nat.log 2 (6 + 16 * (2 * mC)) ≤ D + 4 := by
      have := Nat.log_lt_of_lt_pow (by omega) hlt; omega
    have hsum : Nat.log 2 (6 + 16 * (2 * mC)) + WideWord.kWidthOf (2 * mC) L * 4 + 3 ≤
        4 * (limbMul + 10) * D ^ 2 := by nlinarith
    calc c_AN * (Nat.log 2 (6 + 16 * (2 * mC)) + WideWord.kWidthOf (2 * mC) L * 4 + 3)
        ≤ c * (4 * (limbMul + 10) * D ^ 2) := Nat.mul_le_mul hc_ge hsum
      _ = Cls * D ^ 2 := by dsimp only [Cls]; ring
  set L_sim := WideWord.lsstLSimMin c_AN nC (2 * mC) L 4
  have hLsim : L_sim ≤ Cls * D ^ 2 := max_le (le_trans hkw (by
    have : limbMul + 7 ≤ Cls := by dsimp only [Cls]; nlinarith
    exact Nat.mul_le_mul_right _ this)) hw'
  have hlogn : Real.log ((nC : ℝ) + 2) ≤ (D : ℝ) := by
    have h1 := real_log_nat_add_two_le_log2 nC
    have h2 : Nat.log 2 (nC + 2) + 1 ≤ D := Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
    exact h1.trans (by exact_mod_cast h2)
  have hlogn_nn : 0 ≤ Real.log ((nC : ℝ) + 2) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (nC : ℝ) by positivity])
  have hll : Cited.logLogFactor nC ≤ (D : ℝ) ^ 2 := by
    unfold Cited.logLogFactor
    have hpos : (0 : ℝ) < Real.log ((nC : ℝ) + 2) :=
      Real.log_pos (by linarith [show (0 : ℝ) ≤ (nC : ℝ) by positivity])
    have h2 : Real.log (Real.log ((nC : ℝ) + 2)) ≤ Real.log ((nC : ℝ) + 2) :=
      real_log_le_self_of_pos hpos
    have h3 : Real.log ((nC : ℝ) + 2) * Real.log (Real.log ((nC : ℝ) + 2)) ≤
        Real.log ((nC : ℝ) + 2) * Real.log ((nC : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left h2 hpos.le
    have h4 : Real.log ((nC : ℝ) + 2) * Real.log ((nC : ℝ) + 2) ≤ (D : ℝ) * (D : ℝ) :=
      mul_le_mul hlogn hlogn hpos.le (by positivity)
    linarith [sq (D : ℝ)]
  have hwf : Cited.weightFactor nC (2 ^ (L_sim * 4)) ≤ ((4 * Cls + 7 : ℕ) : ℝ) * (D : ℝ) ^ 2 :=
    weightFactor_le_log2 hD1 hlogn hLsim
  -- Combine all terms of `lsfOverhead`
  have hD_r : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hD2_r : (1 : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast h1D2
  have hD4_le_D6 : (D : ℝ) ^ 4 ≤ (D : ℝ) ^ 6 := by
    rw [show (D : ℝ) ^ 6 = (D : ℝ) ^ 4 * (D : ℝ) ^ 2 by ring]
    exact le_mul_of_one_le_right (by positivity) hD2_r
  have hK_r : max K_AN 1 ≤ (K : ℝ) := Nat.le_ceil _
  have hLsim_r : (L_sim : ℝ) ≤ (Cls : ℝ) * (D : ℝ) ^ 2 := by exact_mod_cast hLsim
  have hW'_r : (WideWord.w'Max c_AN nC (2 * mC) L 4 : ℝ) ≤ (Cls : ℝ) * (D : ℝ) ^ 2 := by exact_mod_cast hw'
  have hLw_r : (canonLw K_AN L nC k : ℝ) ≤ (Cw : ℝ) * (D : ℝ) ^ 2 := by exact_mod_cast hLw
  have hlog2n : ((Nat.log 2 (nC + 2) + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right (by omega : nC + 2 ≤ B)) 1
  have hLsim2 : (L_sim : ℝ) ^ 2 ≤ ((Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 6 := by
    have h1 : (L_sim : ℝ) ^ 2 ≤ ((Cls : ℝ) * (D : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLsim_r 2
    have h2 : ((Cls : ℝ) * (D : ℝ) ^ 2) ^ 2 = ((Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 4 := by push_cast; ring
    have h3 : ((Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 4 ≤ ((Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_left hD4_le_D6 (Nat.cast_nonneg _)
    linarith
  have hLw2 : (canonLw K_AN L nC k : ℝ) ^ 2 ≤ ((Cw ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 6 := by
    have h1 : (canonLw K_AN L nC k : ℝ) ^ 2 ≤ ((Cw : ℝ) * (D : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLw_r 2
    have h2 : ((Cw : ℝ) * (D : ℝ) ^ 2) ^ 2 = ((Cw ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 4 := by push_cast; ring
    have h3 : ((Cw ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 4 ≤ ((Cw ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_left hD4_le_D6 (Nat.cast_nonneg _)
    linarith
  have hlog4 : ((Nat.log 2 (nC + 2) + 1 : ℕ) : ℝ) ^ 4 ≤ (D : ℝ) ^ 6 := by
    have h1 : ((Nat.log 2 (nC + 2) + 1 : ℕ) : ℝ) ^ 4 ≤ (D : ℝ) ^ 4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hlog2n 4
    linarith
  have hmain : (S : ℝ) * (L_sim : ℝ) * (WideWord.w'Max c_AN nC (2 * mC) L 4 : ℝ) *
      (max K_AN 1 * (Cited.logLogFactor nC + Cited.weightFactor nC (2 ^ (L_sim * 4))) + 1) ≤
      ((S * Cls ^ 2 * (K * (4 * Cls + 8) + 1) : ℕ) : ℝ) * (D : ℝ) ^ 6 := by
    have hA : (S : ℝ) * (L_sim : ℝ) * (WideWord.w'Max c_AN nC (2 * mC) L 4 : ℝ) ≤
        ((S * Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 4 := by
      have h1 : (L_sim : ℝ) * (WideWord.w'Max c_AN nC (2 * mC) L 4 : ℝ) ≤
          ((Cls : ℝ) * (D : ℝ) ^ 2) * ((Cls : ℝ) * (D : ℝ) ^ 2) :=
        mul_le_mul hLsim_r hW'_r (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg S)
      have heq1 : (S : ℝ) * ((L_sim : ℝ) * (WideWord.w'Max c_AN nC (2 * mC) L 4 : ℝ)) =
          (S : ℝ) * (L_sim : ℝ) * (WideWord.w'Max c_AN nC (2 * mC) L 4 : ℝ) := by ring
      have heq2 : (S : ℝ) * (((Cls : ℝ) * (D : ℝ) ^ 2) * ((Cls : ℝ) * (D : ℝ) ^ 2)) =
          ((S * Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 4 := by push_cast; ring
      linarith
    have hsum_nn : 0 ≤ Cited.logLogFactor nC + Cited.weightFactor nC (2 ^ (L_sim * 4)) :=
      logLog_add_weightFactor_nonneg nC _ (by
        have : 1 ≤ L_sim := le_trans (by unfold WideWord.kWidthOf; omega) (le_max_left _ _)
        exact le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hB : max K_AN 1 * (Cited.logLogFactor nC + Cited.weightFactor nC (2 ^ (L_sim * 4))) + 1 ≤
        ((K * (4 * Cls + 8) + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2 := by
      have h1 : Cited.logLogFactor nC + Cited.weightFactor nC (2 ^ (L_sim * 4)) ≤
          ((4 * Cls + 8 : ℕ) : ℝ) * (D : ℝ) ^ 2 := by
        have heq : ((4 * Cls + 8 : ℕ) : ℝ) * (D : ℝ) ^ 2 =
            (D : ℝ) ^ 2 + ((4 * Cls + 7 : ℕ) : ℝ) * (D : ℝ) ^ 2 := by push_cast; ring
        linarith
      have h2 := mul_le_mul hK_r h1 hsum_nn (Nat.cast_nonneg K)
      have heq : ((K * (4 * Cls + 8) + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2 =
          (K : ℝ) * (((4 * Cls + 8 : ℕ) : ℝ) * (D : ℝ) ^ 2) + (D : ℝ) ^ 2 := by push_cast; ring
      linarith
    have hB_nn : 0 ≤ max K_AN 1 * (Cited.logLogFactor nC + Cited.weightFactor nC (2 ^ (L_sim * 4))) + 1 := by
      have hKm : (0 : ℝ) ≤ max K_AN 1 := le_trans (by norm_num) (le_max_right _ _)
      linarith [mul_nonneg hKm hsum_nn]
    have hprod := mul_le_mul hA hB hB_nn (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
    have heq : (((S * Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 4) * (((K * (4 * Cls + 8) + 1 : ℕ) : ℝ) * (D : ℝ) ^ 2) =
        ((S * Cls ^ 2 * (K * (4 * Cls + 8) + 1) : ℕ) : ℝ) * (D : ℝ) ^ 6 := by push_cast; ring
    linarith
  rw [hblg3]
  simp only [lsfOverhead, lsstOverheadFactorH]
  have h1D6_r : (1 : ℝ) ≤ (D : ℝ) ^ 6 := by exact_mod_cast Nat.one_le_pow 6 D hD1
  have hCov_eq : (Cov : ℝ) * ((D ^ 6 : ℕ) : ℝ) =
      ((Cls ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 6 +
      ((S * Cls ^ 2 * (K * (4 * Cls + 8) + 1) : ℕ) : ℝ) * (D : ℝ) ^ 6 +
      (D : ℝ) ^ 6 + ((Cw ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ 6 + (D : ℝ) ^ 6 := by
    dsimp only [Cov]; push_cast; ring
  rw [hCov_eq]
  exact add_le_add (add_le_add (add_le_add (add_le_add hLsim2 hmain) hlog4) hLw2) h1D6_r

set_option maxHeartbeats 600000 in
/-- Total `init` cost bound: `compInitCost` + wrapper overhead ≤ `compAsmMul * (G.n + G.m + 1 +
k * lsfInitSize G * bundleLogFactor M N ^ 3)`. -/
theorem compAsmInitCost_le {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {k L P_fp M N capExp limbMul : ℕ} {G : MGraph}
    (hk : 1 ≤ k) (hG_val : G.IsValid) (hGn : G.n ≤ N) (hGm : G.m ≤ M)
    (hP : P_fp ≤ 4 * L) (hkCap : k ≤ (M + N + 2) ^ capExp)
    (hL : L ≤ limbMul * bundleLogFactor M N)
    (g0Ptr lenArr L_w vCap eCap bComp : ℕ) :
    let W := canonicalLSFWindowImpl Q_AN c_AN K_AN hQ L P_fp
    compInitCost W k G [g0Ptr, lenArr, L, P_fp, k, L_w, vCap, eCap, bComp] +
      2000 * k * G.m * (Nat.log 2 (G.m + 2) + 1) +
      (140 * G.n + 600 * G.m +
        (if G.m = 0 then 0 else 20 * Nat.log 2 (k + 1) + 40 * Nat.log 2 (G.n + 2)) + 400) ≤
      compAsmMul Q_AN c_AN K_AN capExp limbMul *
        (G.n + G.m + 1 + k * lsfInitSize G * bundleLogFactor M N ^ 3) := by
  intro W
  have hci : compInitCost W k G [g0Ptr, lenArr, L, P_fp, k, L_w, vCap, eCap, bComp] =
      compInitLinMul * (G.n + G.m + 1) +
        (edgefulComps G).sum (fun C =>
          lsfWindowCost Q_AN c_AN K_AN 4 L P_fp k (compGraph G C).n (compGraph G C).m +
            k * (3000 * ((compGraph G C).n + 1) * (Nat.log 2 ((compGraph G C).n + 2) + 1)) +
            compInitCompMul * ((compGraph G C).n + (compGraph G C).m + 1)) := rfl
  rw [hci]
  clear W hQ hci
  by_cases hGm0 : G.m = 0
  · have hedg_empty : edgefulComps G = ∅ := by
      ext C; simp only [edgefulComps, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _
      have hmC : (compGraph G C).m ≤ G.m := Finset.card_le_card (Finset.filter_subset _ _)
      omega
    rw [hedg_empty, hGm0]; simp only [Finset.sum_empty, add_zero, mul_zero, zero_mul, ↓reduceIte]
    unfold compInitLinMul
    have h1 : 800 * (G.n + 0 + 1) + (140 * G.n + 600 * 0 + 0 + 400) ≤ 20000 * (G.n + 0 + 1) := by omega
    have hM20k : 20000 ≤ compAsmMul Q_AN c_AN K_AN capExp limbMul := by
      unfold compAsmMul; exact Nat.le_add_left _ _
    have h2 : 20000 * (G.n + 0 + 1) ≤
        compAsmMul Q_AN c_AN K_AN capExp limbMul * (G.n + 0 + 1 + k * lsfInitSize G * bundleLogFactor M N ^ 3) :=
      Nat.mul_le_mul hM20k (Nat.le_add_right _ _)
    exact h1.trans h2
  simp only [hGm0, ↓reduceIte]
  have hlsf1 : 1 ≤ lsfInitSize G := by
    have htot := components_sum_m G hG_val
    have hpos : 0 < (components G).sum (fun C => (compGraph G C).m) := by omega
    obtain ⟨C, hC_mem, hCm⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : (components G).sum (fun C => (compGraph G C).m) ≠ 0)
    have hC_edg : C ∈ (components G).filter (fun C => 1 ≤ (compGraph G C).m) :=
      Finset.mem_filter.mpr ⟨hC_mem, by omega⟩
    unfold lsfInitSize
    exact le_trans (by omega : 1 ≤ (compGraph G C).m + (compGraph G C).n + 1)
      (Finset.single_le_sum (f := fun C => (compGraph G C).m + (compGraph G C).n + 1)
        (fun _ _ => Nat.zero_le _) hC_edg)
  unfold compAsmMul
  simp only [lsfWindowCost]
  generalize (lemma55Module Q_AN c_AN K_AN 4).regBound = R
  set D := Nat.log 2 (M + N + 2) + 1
  set c := max c_AN 1
  set K := Nat.ceil (max K_AN 1)
  set S := WideWord.simScale Q_AN
  set Cw := limbMul + capExp + 130
  set Cls := 4 * c * (limbMul + 10)
  set Cov := Cls ^ 2 + S * Cls ^ 2 * (K * (4 * Cls + 8) + 1) + Cw ^ 2 + 2
  set Cl55 := lsfInitCostFactor * (Cov + 1) + 2002000 * (limbMul + 1) * Cw ^ 2 + 20000
  have hD1 : 1 ≤ D := by omega
  have hblg : bundleLogFactor M N = D ^ 2 := rfl
  have hblg3 : bundleLogFactor M N ^ 3 = D ^ 6 := by rw [hblg, ← pow_mul]
  have h1D2 : 1 ≤ D ^ 2 := Nat.one_le_pow 2 D hD1
  have h1D4 : 1 ≤ D ^ 4 := Nat.one_le_pow 4 D hD1
  have h1D5 : 1 ≤ D ^ 5 := Nat.one_le_pow 5 D hD1
  have h1D6 : 1 ≤ D ^ 6 := Nat.one_le_pow 6 D hD1
  have hD_D2 : D ≤ D ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right D hD1
  have hD_D6 : D ≤ D ^ 6 := by rw [show D ^ 6 = D * D ^ 5 by ring]; exact Nat.le_mul_of_pos_right D h1D5
  have hD2_D6 : D ^ 2 ≤ D ^ 6 := by rw [show D ^ 6 = D ^ 2 * D ^ 4 by ring]; exact Nat.le_mul_of_pos_right _ h1D4
  have hD4_D6 : D ^ 4 ≤ D ^ 6 := by rw [show D ^ 6 = D ^ 4 * D ^ 2 by ring]; exact Nat.le_mul_of_pos_right _ h1D2
  have hCw1 : 1 ≤ Cw := by dsimp only [Cw]; omega
  have hCw_sq : Cw ≤ Cw ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right Cw hCw1
  -- Per edgeful component bound
  have hcomp : ∀ C ∈ edgefulComps G,
      let nC := (compGraph G C).n
      let mC := (compGraph G C).m
      (2 * R + 10) * lemma55Cost Q_AN c_AN K_AN 4 L (canonLw K_AN L nC k) P_fp k nC mC +
        k * (3000 * (nC + 1) * (Nat.log 2 (nC + 2) + 1)) +
        compInitCompMul * (nC + mC + 1) ≤
      (2 * (2 * R + 10) * Cl55) * (k * (mC + nC + 1) * D ^ 6) := by
    intro C hC nC mC
    have hC_mem : C ∈ components G := (Finset.mem_filter.mp hC).1
    have hnC : nC ≤ N := le_trans (compGraph_n_le hC_mem) hGn
    have hmC : mC ≤ M := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hGm
    have hLwC : canonLw K_AN L nC k ≤ Cw * D ^ 2 := by
      have h1 := canonLw_le_readout2_of_rho (L_in := L) (n0 := nC) (k_nat := k)
        (M := M) (N := N) (capExp := capExp) hRho hnC hkCap
      unfold sparseCoreReadout2LimbConst at h1
      change canonLw K_AN L nC k ≤ L + (capExp + 128) * D at h1
      rw [hblg] at hL
      have h2 : (capExp + 128) * D ≤ (capExp + 130) * D ^ 2 := Nat.mul_le_mul (by omega) hD_D2
      have h3 : (limbMul + capExp + 130) * D ^ 2 = limbMul * D ^ 2 + (capExp + 130) * D ^ 2 := by ring
      dsimp only [Cw]; omega
    have hov := lsfOverhead_le_log6 (Q_AN := Q_AN) (c_AN := c_AN) (K_AN := K_AN) hRho hnC hmC hkCap hL
    have hinitC : lsfInitCostFactor * Nat.ceil (((mC + nC + 1 : ℕ) : ℝ) *
        lsfOverhead Q_AN c_AN K_AN nC mC L (canonLw K_AN L nC k) 4) ≤
        lsfInitCostFactor * (Cov + 1) * (mC + nC + 1) * D ^ 6 := by
      have hceil : Nat.ceil (((mC + nC + 1 : ℕ) : ℝ) *
          lsfOverhead Q_AN c_AN K_AN nC mC L (canonLw K_AN L nC k) 4) ≤
          (Cov + 1) * (mC + nC + 1) * D ^ 6 := by
        apply Nat.ceil_le.mpr
        rw [hblg3] at hov
        have h1 := mul_le_mul_of_nonneg_left hov (Nat.cast_nonneg (mC + nC + 1))
        have h2 : ((mC + nC + 1 : ℕ) : ℝ) * ((Cov : ℝ) * ((D ^ 6 : ℕ) : ℝ)) ≤
            (((Cov + 1) * (mC + nC + 1) * D ^ 6 : ℕ) : ℝ) := by
          have hnn : (0 : ℝ) ≤ ((mC + nC + 1 : ℕ) : ℝ) * (D : ℝ) ^ 6 :=
            mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
          have heq : (((Cov + 1) * (mC + nC + 1) * D ^ 6 : ℕ) : ℝ) =
              ((mC + nC + 1 : ℕ) : ℝ) * ((Cov : ℝ) * ((D ^ 6 : ℕ) : ℝ)) +
              ((mC + nC + 1 : ℕ) : ℝ) * (D : ℝ) ^ 6 := by push_cast; ring
          linarith
        exact h1.trans h2
      have h2 := Nat.mul_le_mul_left lsfInitCostFactor hceil
      have heq : lsfInitCostFactor * ((Cov + 1) * (mC + nC + 1) * D ^ 6) =
          lsfInitCostFactor * (Cov + 1) * (mC + nC + 1) * D ^ 6 := by ring
      omega
    have hmwu : mwuEdgeStepCost L (canonLw K_AN L nC k) P_fp ≤
        2000000 * (limbMul + 1) * Cw ^ 2 * D ^ 6 :=
      mwuEdgeStepCost_le_log6 hD1 (canonLw_ge_Lin K_AN L nC k) (by rwa [hblg] at hL) hP hLwC hCw1
    have hl55 : lemma55Cost Q_AN c_AN K_AN 4 L (canonLw K_AN L nC k) P_fp k nC mC ≤
        Cl55 * (k * (mC + nC + 1) * D ^ 6) := by
      unfold lemma55Cost
      dsimp only
      have h1 : mC * (mwuEdgeStepCost L (canonLw K_AN L nC k) P_fp + 80) + 200 ≤
          (2000000 * (limbMul + 1) * Cw ^ 2 + 300) * (mC + nC + 1) * D ^ 6 := by
        have hm1 : mC ≤ mC + nC + 1 := by omega
        have h80_d6 : 80 ≤ 80 * D ^ 6 := Nat.le_mul_of_pos_right 80 h1D6
        have h80 : mwuEdgeStepCost L (canonLw K_AN L nC k) P_fp + 80 ≤
            (2000000 * (limbMul + 1) * Cw ^ 2 + 80) * D ^ 6 := by
          rw [Nat.add_mul]; exact Nat.add_le_add hmwu h80_d6
        have hmul := Nat.mul_le_mul hm1 h80
        have h200 : 200 ≤ 200 * ((mC + nC + 1) * D ^ 6) :=
          Nat.le_mul_of_pos_right 200 (Nat.mul_pos (Nat.succ_pos _) h1D6)
        have hre : (mC + nC + 1) * ((2000000 * (limbMul + 1) * Cw ^ 2 + 80) * D ^ 6) =
            (2000000 * (limbMul + 1) * Cw ^ 2 + 80) * ((mC + nC + 1) * D ^ 6) := by ring
        have hre2 : (2000000 * (limbMul + 1) * Cw ^ 2 + 300) * (mC + nC + 1) * D ^ 6 =
            (2000000 * (limbMul + 1) * Cw ^ 2 + 80) * ((mC + nC + 1) * D ^ 6) +
            200 * ((mC + nC + 1) * D ^ 6) + 20 * ((mC + nC + 1) * D ^ 6) := by ring
        omega
      have h2 : 500 * canonLw K_AN L nC k * canonLw K_AN L nC k + 800 * canonLw K_AN L nC k +
          20 * Nat.log 2 (nC + 2) + 30 * mC + 1000 ≤
          (1500 * Cw ^ 2 + 2000) * (k * (mC + nC + 1) * D ^ 6) := by
        have hLw2 : canonLw K_AN L nC k * canonLw K_AN L nC k ≤ Cw ^ 2 * D ^ 6 := by
          have ha := Nat.mul_le_mul hLwC hLwC
          have heq : Cw * D ^ 2 * (Cw * D ^ 2) = Cw ^ 2 * D ^ 4 := by ring
          exact (ha.trans_eq heq).trans (Nat.mul_le_mul_left _ hD4_D6)
        have hLw1 : canonLw K_AN L nC k ≤ Cw ^ 2 * D ^ 6 :=
          hLwC.trans (Nat.mul_le_mul hCw_sq hD2_D6)
        have hlogn : Nat.log 2 (nC + 2) ≤ D ^ 6 :=
          le_trans (Nat.le_succ_of_le (Nat.log_mono_right (by omega : nC + 2 ≤ M + N + 2))) hD_D6
        have hkmn : 1 ≤ k * (mC + nC + 1) := Nat.mul_pos hk (Nat.succ_pos _)
        have hlogn' : Nat.log 2 (nC + 2) ≤ k * (mC + nC + 1) * D ^ 6 :=
          hlogn.trans (Nat.le_mul_of_pos_left _ hkmn)
        have hm_kmn : mC ≤ k * (mC + nC + 1) * D ^ 6 := by
          have : mC ≤ 1 * (mC + nC + 1) * 1 := by omega
          exact this.trans (Nat.mul_le_mul (Nat.mul_le_mul hk le_rfl) h1D6)
        have hLw2' : Cw ^ 2 * D ^ 6 ≤ Cw ^ 2 * (k * (mC + nC + 1) * D ^ 6) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hkmn)
        have h500 : 500 * canonLw K_AN L nC k * canonLw K_AN L nC k =
            500 * (canonLw K_AN L nC k * canonLw K_AN L nC k) := Nat.mul_assoc _ _ _
        rw [h500]
        have h1000 : 1000 ≤ 1000 * (k * (mC + nC + 1) * D ^ 6) :=
          Nat.le_mul_of_pos_right 1000 (Nat.mul_pos hkmn h1D6)
        have hre : (1500 * Cw ^ 2 + 2000) * (k * (mC + nC + 1) * D ^ 6) =
            1500 * (Cw ^ 2 * (k * (mC + nC + 1) * D ^ 6)) +
            2000 * (k * (mC + nC + 1) * D ^ 6) := by ring
        omega
      have hbody : lsfInitCostFactor * Nat.ceil (((mC + nC + 1 : ℕ) : ℝ) *
            lsfOverhead Q_AN c_AN K_AN nC mC L (canonLw K_AN L nC k) 4) +
            mC * (mwuEdgeStepCost L (canonLw K_AN L nC k) P_fp + 80) + 200 ≤
          (lsfInitCostFactor * (Cov + 1) + 2000000 * (limbMul + 1) * Cw ^ 2 + 300) *
            (mC + nC + 1) * D ^ 6 := by
        have hre : (lsfInitCostFactor * (Cov + 1) + 2000000 * (limbMul + 1) * Cw ^ 2 + 300) *
            (mC + nC + 1) * D ^ 6 =
            lsfInitCostFactor * (Cov + 1) * (mC + nC + 1) * D ^ 6 +
            (2000000 * (limbMul + 1) * Cw ^ 2 + 300) * (mC + nC + 1) * D ^ 6 := by ring
        omega
      have hkbody := Nat.mul_le_mul_left k hbody
      have hre2 : k * ((lsfInitCostFactor * (Cov + 1) + 2000000 * (limbMul + 1) * Cw ^ 2 + 300) *
            (mC + nC + 1) * D ^ 6) =
          (lsfInitCostFactor * (Cov + 1) + 2000000 * (limbMul + 1) * Cw ^ 2 + 300) *
            (k * (mC + nC + 1) * D ^ 6) := by ring
      have hCl55_ge : (lsfInitCostFactor * (Cov + 1) + 2000000 * (limbMul + 1) * Cw ^ 2 + 300) +
          (1500 * Cw ^ 2 + 2000) ≤ Cl55 := by
        dsimp only [Cl55]
        have h1500 : 1500 * Cw ^ 2 ≤ 2000 * ((limbMul + 1) * Cw ^ 2) :=
          le_trans (Nat.mul_le_mul_right _ (by decide : 1500 ≤ 2000))
            (Nat.mul_le_mul_left 2000 (Nat.le_mul_of_pos_left _ (Nat.succ_pos limbMul)))
        have hre : 2002000 * (limbMul + 1) * Cw ^ 2 =
            2000000 * (limbMul + 1) * Cw ^ 2 + 2000 * ((limbMul + 1) * Cw ^ 2) := by ring
        linarith
      have hsum_bd := Nat.mul_le_mul_right (k * (mC + nC + 1) * D ^ 6) hCl55_ge
      rw [Nat.add_mul] at hsum_bd
      linarith
    have hwin : (2 * R + 10) * lemma55Cost Q_AN c_AN K_AN 4 L (canonLw K_AN L nC k) P_fp k nC mC ≤
        (2 * R + 10) * Cl55 * (k * (mC + nC + 1) * D ^ 6) := by
      have h1 := Nat.mul_le_mul_left (2 * R + 10) hl55
      simpa only [Nat.mul_assoc] using h1
    have hlog_nC : Nat.log 2 (nC + 2) + 1 ≤ D ^ 6 :=
      le_trans (Nat.add_le_add_right (Nat.log_mono_right (by omega : nC + 2 ≤ M + N + 2)) 1) hD_D6
    have hrest : k * (3000 * (nC + 1) * (Nat.log 2 (nC + 2) + 1)) + compInitCompMul * (nC + mC + 1) ≤
        4000 * (k * (mC + nC + 1) * D ^ 6) := by
      unfold compInitCompMul
      have h1 : k * (3000 * (nC + 1) * (Nat.log 2 (nC + 2) + 1)) ≤ 3000 * (k * (mC + nC + 1) * D ^ 6) := by
        have ha : (nC + 1) * (Nat.log 2 (nC + 2) + 1) ≤ (mC + nC + 1) * D ^ 6 :=
          Nat.mul_le_mul (by omega) hlog_nC
        have hb := Nat.mul_le_mul_left k (Nat.mul_le_mul_left 3000 ha)
        have heq1 : k * (3000 * ((nC + 1) * (Nat.log 2 (nC + 2) + 1))) =
            k * (3000 * (nC + 1) * (Nat.log 2 (nC + 2) + 1)) := by ring
        have heq2 : k * (3000 * ((mC + nC + 1) * D ^ 6)) = 3000 * (k * (mC + nC + 1) * D ^ 6) := by ring
        linarith
      have h2 : 800 * (nC + mC + 1) ≤ 1000 * (k * (mC + nC + 1) * D ^ 6) := by
        have : nC + mC + 1 ≤ k * (mC + nC + 1) * D ^ 6 := by
          have : 1 * (mC + nC + 1) * 1 ≤ k * (mC + nC + 1) * D ^ 6 :=
            Nat.mul_le_mul (Nat.mul_le_mul hk le_rfl) h1D6
          linarith
        linarith
      linarith
    have h4000 : 4000 ≤ (2 * R + 10) * Cl55 := by
      have h20k : 20000 ≤ Cl55 := by dsimp only [Cl55]; exact Nat.le_add_left _ _
      exact le_trans (by decide : 4000 ≤ 10 * 20000) (Nat.mul_le_mul (by omega) h20k)
    have hrest' := hrest.trans (Nat.mul_le_mul_right _ h4000)
    have h2eq : 2 * (2 * R + 10) * Cl55 * (k * (mC + nC + 1) * D ^ 6) =
        (2 * R + 10) * Cl55 * (k * (mC + nC + 1) * D ^ 6) +
        (2 * R + 10) * Cl55 * (k * (mC + nC + 1) * D ^ 6) := by ring
    omega
  -- Sum over `edgefulComps G`: `∑ (mC + nC + 1) = lsfInitSize G`
  have hsum_sz : (edgefulComps G).sum (fun C => (compGraph G C).m + (compGraph G C).n + 1) ≤
      2 * lsfInitSize G := by
    have heq : (edgefulComps G).sum (fun C => (compGraph G C).m + (compGraph G C).n + 1) =
        lsfInitSize G := rfl
    omega
  have hsum_cost : (edgefulComps G).sum (fun C =>
      (2 * R + 10) * lemma55Cost Q_AN c_AN K_AN 4 L (canonLw K_AN L (compGraph G C).n k) P_fp k
        (compGraph G C).n (compGraph G C).m +
        k * (3000 * ((compGraph G C).n + 1) * (Nat.log 2 ((compGraph G C).n + 2) + 1)) +
        compInitCompMul * ((compGraph G C).n + (compGraph G C).m + 1)) ≤
      (4 * (2 * R + 10) * Cl55) * (k * lsfInitSize G * D ^ 6) := by
    calc _ ≤ (edgefulComps G).sum (fun C =>
            (2 * (2 * R + 10) * Cl55) * (k * ((compGraph G C).m + (compGraph G C).n + 1) * D ^ 6)) :=
          Finset.sum_le_sum fun C hC => hcomp C hC
      _ = (2 * (2 * R + 10) * Cl55) * (k * D ^ 6 *
            (edgefulComps G).sum (fun C => (compGraph G C).m + (compGraph G C).n + 1)) := by
          rw [← Finset.mul_sum]; congr 1; rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun C _ => by ring
      _ ≤ (2 * (2 * R + 10) * Cl55) * (k * D ^ 6 * (2 * lsfInitSize G)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsum_sz)
      _ = (4 * (2 * R + 10) * Cl55) * (k * lsfInitSize G * D ^ 6) := by ring
  -- Wrapper + linear prefix cost
  have hlogk : Nat.log 2 (k + 1) ≤ capExp * D + 1 := by
    have hB_lt : M + N + 2 < 2 ^ D := Nat.lt_pow_succ_log_self (by decide) (M + N + 2)
    have hpow : (M + N + 2) ^ capExp ≤ (2 ^ D) ^ capExp := Nat.pow_le_pow_left hB_lt.le capExp
    have h1 : k + 1 < 2 ^ (capExp * D + 2) := by
      have h3 : (2 ^ D) ^ capExp = 2 ^ (capExp * D) := by rw [← pow_mul, mul_comm]
      have h4 : 2 ^ (capExp * D + 2) = 4 * 2 ^ (capExp * D) := by rw [pow_succ, pow_succ]; ring
      have : 1 ≤ 2 ^ (capExp * D) := Nat.one_le_pow _ _ (by decide)
      omega
    have := Nat.log_lt_of_lt_pow (by omega) h1
    omega
  have hlogn : Nat.log 2 (G.n + 2) ≤ D := Nat.le_succ_of_le (Nat.log_mono_right (by omega))
  have hGm_le_lsf : G.m ≤ lsfInitSize G := by
    have htot := components_sum_m G hG_val
    have hfilt : (components G).sum (fun C => (compGraph G C).m) =
        ((components G).filter fun C => 1 ≤ (compGraph G C).m).sum (fun C => (compGraph G C).m) := by
      rw [← Finset.sum_filter_add_sum_filter_not (components G) (fun C => 1 ≤ (compGraph G C).m)]
      have h0 : ((components G).filter fun C => ¬ 1 ≤ (compGraph G C).m).sum (fun C => (compGraph G C).m) = 0 :=
        Finset.sum_eq_zero fun C hC => by have := (Finset.mem_filter.mp hC).2; omega
      omega
    have hle : ((components G).filter fun C => 1 ≤ (compGraph G C).m).sum (fun C => (compGraph G C).m) ≤
        lsfInitSize G := by
      unfold lsfInitSize
      exact Finset.sum_le_sum fun C _ => by omega
    omega
  have hlogm : Nat.log 2 (G.m + 2) + 1 ≤ D := Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
  have hspPhi : 2000 * k * G.m * (Nat.log 2 (G.m + 2) + 1) ≤ 2000 * (k * lsfInitSize G * D ^ 6) := by
    have h1 : G.m * (Nat.log 2 (G.m + 2) + 1) ≤ lsfInitSize G * D ^ 6 :=
      Nat.mul_le_mul hGm_le_lsf (hlogm.trans hD_D6)
    have h2 := Nat.mul_le_mul_left (2000 * k) h1
    have heq1 : 2000 * k * (G.m * (Nat.log 2 (G.m + 2) + 1)) = 2000 * k * G.m * (Nat.log 2 (G.m + 2) + 1) := by ring
    have heq2 : 2000 * k * (lsfInitSize G * D ^ 6) = 2000 * (k * lsfInitSize G * D ^ 6) := by ring
    omega
  have hlin : compInitLinMul * (G.n + G.m + 1) +
      2000 * k * G.m * (Nat.log 2 (G.m + 2) + 1) +
      (140 * G.n + 600 * G.m + 20 * Nat.log 2 (k + 1) + 40 * Nat.log 2 (G.n + 2) + 400) ≤
      (250000 * (Cw + 1) + 20000) * (G.n + G.m + 1 + k * lsfInitSize G * D ^ 6) := by
    unfold compInitLinMul
    have hcapD : 20 * (capExp * D + 1) ≤ 250000 * (Cw + 1) * (k * lsfInitSize G * D ^ 6) := by
      have h1 : capExp ≤ Cw := by dsimp only [Cw]; omega
      have h2 : 1 ≤ k * lsfInitSize G := Nat.mul_pos hk hlsf1
      have h3 : capExp * D ≤ Cw * (k * lsfInitSize G * D ^ 6) := by
        have := Nat.mul_le_mul h1 hD_D6
        exact this.trans (Nat.mul_le_mul_left Cw (Nat.le_mul_of_pos_left _ h2))
      have h4 : 1 ≤ Cw * (k * lsfInitSize G * D ^ 6) := Nat.mul_pos hCw1 (Nat.mul_pos h2 h1D6)
      have h5 : Cw * (k * lsfInitSize G * D ^ 6) ≤ (Cw + 1) * (k * lsfInitSize G * D ^ 6) :=
        Nat.mul_le_mul_right _ (Nat.le_succ Cw)
      have h6 : 250000 * (Cw + 1) * (k * lsfInitSize G * D ^ 6) =
          250000 * ((Cw + 1) * (k * lsfInitSize G * D ^ 6)) := Nat.mul_assoc _ _ _
      omega
    have h40D : 40 * D ≤ 1000 * (k * lsfInitSize G * D ^ 6) := by
      have h2 : 1 ≤ k * lsfInitSize G := Nat.mul_pos hk hlsf1
      have : D ≤ k * lsfInitSize G * D ^ 6 := hD_D6.trans (Nat.le_mul_of_pos_left _ h2)
      omega
    have hadd_ge : (250000 * (Cw + 1) + 20000) * (G.n + G.m + 1 + k * lsfInitSize G * D ^ 6) =
        (250000 * (Cw + 1) + 20000) * (G.n + G.m + 1) +
        250000 * (Cw + 1) * (k * lsfInitSize G * D ^ 6) +
        20000 * (k * lsfInitSize G * D ^ 6) := by ring
    have hgnm : 20000 * (G.n + G.m + 1) ≤ (250000 * (Cw + 1) + 20000) * (G.n + G.m + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    linarith
  rw [hblg3]
  change compInitLinMul * (G.n + G.m + 1) +
      (edgefulComps G).sum (fun C =>
        (2 * R + 10) * lemma55Cost Q_AN c_AN K_AN 4 L (canonLw K_AN L (compGraph G C).n k) P_fp k
          (compGraph G C).n (compGraph G C).m +
          k * (3000 * ((compGraph G C).n + 1) * (Nat.log 2 ((compGraph G C).n + 2) + 1)) +
          compInitCompMul * ((compGraph G C).n + (compGraph G C).m + 1)) +
      2000 * k * G.m * (Nat.log 2 (G.m + 2) + 1) +
      (140 * G.n + 600 * G.m + (20 * Nat.log 2 (k + 1) + 40 * Nat.log 2 (G.n + 2)) + 400) ≤
    (4 * (2 * R + 10) * Cl55 + 250000 * (Cw + 1) + 20000) *
      (G.n + G.m + 1 + k * lsfInitSize G * D ^ 6)
  rw [Nat.add_assoc (4 * (2 * R + 10) * Cl55), Nat.add_mul]
  have hre : ∀ a b c d : ℕ, a + b + c + d = b + (a + c + d) := fun a b c d => by omega
  rw [hre]
  have hlin' : compInitLinMul * (G.n + G.m + 1) +
      2000 * k * G.m * (Nat.log 2 (G.m + 2) + 1) +
      (140 * G.n + 600 * G.m + (20 * Nat.log 2 (k + 1) + 40 * Nat.log 2 (G.n + 2)) + 400) ≤
      (250000 * (Cw + 1) + 20000) * (G.n + G.m + 1 + k * lsfInitSize G * D ^ 6) := by
    simpa only [Nat.add_assoc] using hlin
  exact (Nat.add_le_add hsum_cost hlin').trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) _)

/-- Batch cost bound: `compBatchCost_polylog` + copy + `dgApplyBatch` + wrapper overhead
≤ `compAsmMul * ((k + 1) * (words + 1)) * bundleLogFactor M N`. -/
theorem compAsmBatchCost_le {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {k L M N capExp limbMul n0 words : ℕ}
    (hn0 : n0 ≤ N) (hkCap : k ≤ (M + N + 2) ^ capExp)
    (hL : L ≤ limbMul * bundleLogFactor M N) :
    let L_w := canonLw K_AN L n0 k
    (200000 * (L_w + 1) + 3000) * k * (words + 1) + (20 * words + 20) + (670 * words + 30) + 150 ≤
      compAsmMul Q_AN c_AN K_AN capExp limbMul * ((k + 1) * (words + 1)) * bundleLogFactor M N := by
  intro L_w
  set D := Nat.log 2 (M + N + 2) + 1
  set Cw := limbMul + capExp + 130
  have hD1 : 1 ≤ D := by omega
  have hblg : bundleLogFactor M N = D ^ 2 := rfl
  have h1blg : 1 ≤ bundleLogFactor M N := by rw [hblg]; exact Nat.one_le_pow 2 D hD1
  have hLw : L_w ≤ Cw * bundleLogFactor M N := by
    have h1 := canonLw_le_readout2_of_rho (L_in := L) (n0 := n0) (k_nat := k)
      (M := M) (N := N) (capExp := capExp) hRho hn0 hkCap
    unfold sparseCoreReadout2LimbConst at h1
    change L_w ≤ L + (capExp + 128) * D at h1
    have h2 : (capExp + 128) * D ≤ (capExp + 130) * D ^ 2 := Nat.mul_le_mul (by omega) (by nlinarith)
    have h3 : (limbMul + capExp + 130) * D ^ 2 = limbMul * D ^ 2 + (capExp + 130) * D ^ 2 := by ring
    dsimp only [Cw]; rw [hblg] at hL ⊢; omega
  have hLw1 : L_w + 1 ≤ (Cw + 1) * bundleLogFactor M N := by
    have heq : (Cw + 1) * bundleLogFactor M N = Cw * bundleLogFactor M N + bundleLogFactor M N := by ring
    omega
  have hM_ge : 250000 * (Cw + 1) + 20000 ≤ compAsmMul Q_AN c_AN K_AN capExp limbMul := by
    unfold compAsmMul; dsimp only [Cw]; omega
  have h1 : (200000 * (L_w + 1) + 3000) * k * (words + 1) ≤
      (200000 * (Cw + 1) + 3000) * ((k + 1) * (words + 1)) * bundleLogFactor M N := by
    have ha : 200000 * (L_w + 1) + 3000 ≤ (200000 * (Cw + 1) + 3000) * bundleLogFactor M N := by nlinarith
    have hb := Nat.mul_le_mul ha (Nat.mul_le_mul (show k ≤ k + 1 by omega) (le_refl (words + 1)))
    have heq1 : (200000 * (L_w + 1) + 3000) * (k * (words + 1)) =
        (200000 * (L_w + 1) + 3000) * k * (words + 1) := by ring
    have heq2 : (200000 * (Cw + 1) + 3000) * bundleLogFactor M N * ((k + 1) * (words + 1)) =
        (200000 * (Cw + 1) + 3000) * ((k + 1) * (words + 1)) * bundleLogFactor M N := by ring
    omega
  have h2 : (20 * words + 20) + (670 * words + 30) + 150 ≤
      1000 * ((k + 1) * (words + 1)) * bundleLogFactor M N := by
    have hle : words + 1 ≤ (k + 1) * (words + 1) * bundleLogFactor M N := by
      have : 1 * (words + 1) * 1 ≤ (k + 1) * (words + 1) * bundleLogFactor M N :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) h1blg
      omega
    rw [Nat.mul_assoc]
    exact le_trans (by omega) (Nat.mul_le_mul_left 1000 hle)
  have h3 : (200000 * (Cw + 1) + 4000) * ((k + 1) * (words + 1)) * bundleLogFactor M N ≤
      compAsmMul Q_AN c_AN K_AN capExp limbMul * ((k + 1) * (words + 1)) * bundleLogFactor M N :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hadd : (200000 * (Cw + 1) + 4000) * ((k + 1) * (words + 1)) * bundleLogFactor M N =
      (200000 * (Cw + 1) + 3000) * ((k + 1) * (words + 1)) * bundleLogFactor M N +
      1000 * ((k + 1) * (words + 1)) * bundleLogFactor M N := by ring
  omega

/-- Export cost bound: `compExportCost` + wrapper overhead
≤ `compAsmMul * ((G.n + G.m + 1) * bundleLogFactor M N)`. -/
theorem compAsmExportCost_le {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hRho : Nat.log 2 (lemma55RhoConst K_AN + 1) ≤ 65)
    {k L M N capExp limbMul n0 nG mG mT mF : ℕ}
    (hn0 : n0 ≤ N) (hkCap : k ≤ (M + N + 2) ^ capExp)
    (hL : L ≤ limbMul * bundleLogFactor M N)
    (hmT : mT ≤ mG) (hmF : mF ≤ mG) :
    let L_w := canonLw K_AN L n0 k
    450 * nG + 180 * mT + 100 * mF + 40 * mG * L_w + 100 * mG + 500 + 100 ≤
      compAsmMul Q_AN c_AN K_AN capExp limbMul * ((nG + mG + 1) * bundleLogFactor M N) := by
  intro L_w
  set D := Nat.log 2 (M + N + 2) + 1
  set Cw := limbMul + capExp + 130
  have hD1 : 1 ≤ D := by omega
  have hblg : bundleLogFactor M N = D ^ 2 := rfl
  have h1blg : 1 ≤ bundleLogFactor M N := by rw [hblg]; exact Nat.one_le_pow 2 D hD1
  have hLw : L_w ≤ Cw * bundleLogFactor M N := by
    have h1 := canonLw_le_readout2_of_rho (L_in := L) (n0 := n0) (k_nat := k)
      (M := M) (N := N) (capExp := capExp) hRho hn0 hkCap
    unfold sparseCoreReadout2LimbConst at h1
    change L_w ≤ L + (capExp + 128) * D at h1
    have h2 : (capExp + 128) * D ≤ (capExp + 130) * D ^ 2 := Nat.mul_le_mul (by omega) (by nlinarith)
    have h3 : (limbMul + capExp + 130) * D ^ 2 = limbMul * D ^ 2 + (capExp + 130) * D ^ 2 := by ring
    dsimp only [Cw]; rw [hblg] at hL ⊢; omega
  have hM_ge : 40 * Cw + 1000 ≤ compAsmMul Q_AN c_AN K_AN capExp limbMul := by
    unfold compAsmMul; dsimp only [Cw]; omega
  have h1 : 40 * mG * L_w ≤ (40 * Cw) * ((nG + mG + 1) * bundleLogFactor M N) := by
    have ha : mG * L_w ≤ (nG + mG + 1) * (Cw * bundleLogFactor M N) :=
      Nat.mul_le_mul (by omega) hLw
    have hb := Nat.mul_le_mul_left 40 ha
    have heq : 40 * ((nG + mG + 1) * (Cw * bundleLogFactor M N)) =
        (40 * Cw) * ((nG + mG + 1) * bundleLogFactor M N) := by ring
    have heq0 : 40 * (mG * L_w) = 40 * mG * L_w := (Nat.mul_assoc 40 mG L_w).symm
    omega
  have h2 : 450 * nG + 180 * mT + 100 * mF + 100 * mG + 600 ≤
      1000 * ((nG + mG + 1) * bundleLogFactor M N) := by
    have : nG + mG + 1 ≤ (nG + mG + 1) * bundleLogFactor M N := Nat.le_mul_of_pos_right _ h1blg
    omega
  have h3 := Nat.mul_le_mul_right ((nG + mG + 1) * bundleLogFactor M N) hM_ge
  rw [Nat.add_mul] at h3
  omega

end MinCostFlow.SparseCore.Program

