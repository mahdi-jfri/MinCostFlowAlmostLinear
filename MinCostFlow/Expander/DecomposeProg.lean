module

public import MinCostFlow.Expander.DecomposeProgInv
public import MinCostFlow.Expander.DecomposeProgLoop
public import MinCostFlow.ExpanderDecomp.Statement

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic Word RAM `DecomposeImpl` (Theorem 8.5, Theorem B.1, Algorithm 5)

Assembles `decomposeStepBody`, `decomposeLevelLoop`, `decomposeEntry`, and `decomposeProcs`,
proves multi-level loop preservation into `decompProp_of_multiLevel`, and constructs the
deterministic `decomposeImpl : Cited.ExpanderDecomposition → Spanner.DecomposeImpl` meeting
`Spanner.decomposeHeapContract` with `c_ℓ = 1`, `φ_lb m = 1 / maxPhiDenOf K_nat thr m`, and
`decFactor = subpolyB1 C₀_cost`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section


/-! ## 4. Main Specification and `decomposeImpl` -/

private lemma wordSize_twin_le_sub {c n m D : ℕ} {curG : Cited.Graph}
    (hV : curG.IsValid) (hn : curG.n = n) (hnm : n < m) (hm : curG.m ≤ m) (hDn : D * n ≤ 2 * m) :
    2 ^ (wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) + 1) ≤
      2 * (416 * (n + m + 2)) ^ c ∧
    wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) ≤
      5 * c * (Nat.log 2 (n + m + 206) + 1) :=
  two_pow_wordSize_twin_le hV c n m hn hnm hm hDn

private lemma entry_cost_subpoly_le
    {K_nat : ℕ} {C₀_lvl : ℝ}
    (hC₀_nn : 0 ≤ C₀_lvl) (hKn : 1 ≤ K_nat)
    {n m : ℕ} (h1n : 1 ≤ n) (hnm : n < m)
    {C_lvl : ℝ} (hC_lvl_nn : 0 ≤ C_lvl)
    {c_phi c_ell c_lay c_init c_loop c_pack : ℕ}
    (hc_phi : c_phi ≤ 120 * (Nat.log 2 (4 * m + 2) + K_nat * rOf (4 * m) ^ 2 + 4))
    (hc_ell : c_ell ≤ 13 * (Nat.log 2 (m / n) + 1) + 20)
    (hc_lay : c_lay ≤ 13 * (Nat.log 2 (2 * m + 1) + 1) + 250)
    (hc_init : c_init ≤ 60 * m + 100)
    (hc_loop : (c_loop : ℝ) ≤ ↑(Nat.log 2 (m / n) + 1) * (C_lvl * ↑m * subpolyB1 C₀_lvl m + 100) +
        6 * ↑(Nat.log 2 (m / n) + 1) + 4)
    (hc_pack : c_pack ≤ 150 * m + 65 * (Nat.log 2 (m / n) + 1) + 120) :
    let K_dec : ℝ := 13 * (C_lvl + 100) + 120 * (50 + 48 * ↑K_nat) + 2000
    let c_tot := c_phi + (c_ell + (c_lay + (c_init + (c_loop + c_pack + 1) + 1) + 1) + 1) + 1 + 14
    c_tot ≤ ⌈K_dec * (↑m * subpolyB1 (2 + C₀_lvl) m + 1)⌉₊ := by
  have hm2 : 2 ≤ m := by omega
  have hm_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hsb2 : (1 : ℝ) ≤ subpolyB1 2 m := one_le_subpolyB1 (by norm_num) m
  have hsb_lvl : (1 : ℝ) ≤ subpolyB1 C₀_lvl m := one_le_subpolyB1 hC₀_nn m
  have hsb_cost : (1 : ℝ) ≤ subpolyB1 (2 + C₀_lvl) m := one_le_subpolyB1 (by linarith) m
  have hℓ_le_m : Nat.log 2 (m / n) + 1 ≤ m := by
    have h1 := natLog2_add_one_le_self' (Nat.div_pos (le_of_lt hnm) h1n)
    exact le_trans h1 (Nat.div_le_self m n)
  have hℓ_sb : ((Nat.log 2 (m / n) + 1 : ℕ) : ℝ) ≤ 13 * subpolyB1 2 m := by
    have hlog_le : Nat.log 2 (m / n) ≤ Nat.log 2 m := Nat.log_mono_right (Nat.div_le_self m n)
    have h2pow : (2 ^ Nat.log 2 m : ℝ) ≤ (m : ℝ) + 2 := by
      have h := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
      exact_mod_cast (by omega : 2 ^ Nat.log 2 m ≤ m + 2)
    have hreal_log : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log ((m : ℝ) + 2) := by
      have h := Real.log_le_log (by positivity) h2pow
      rwa [Real.log_pow] at h
    have hhalf := half_lt_real_log_two
    have hnat_log : (Nat.log 2 m : ℝ) ≤ 2 * Real.log ((m : ℝ) + 2) := by nlinarith
    have hlog_sb := real_log_add_two_le_sb m
    have hle : ((Nat.log 2 (m / n) + 1 : ℕ) : ℝ) ≤ (Nat.log 2 m : ℝ) + 1 := by
      push_cast; exact_mod_cast (by omega : Nat.log 2 (m / n) + 1 ≤ Nat.log 2 m + 1)
    linarith
  have hc_phi_lin : (c_phi : ℝ) ≤ 120 * (50 + 48 * ↑K_nat) * ↑m * subpolyB1 (2 + C₀_lvl) m := by
    have hlog4m2 : Nat.log 2 (4 * m + 2) ≤ 4 * m + 2 := by
      have := natLog2_add_one_le_self' (by omega : 1 ≤ 4 * m + 2); omega
    have hr2 : rOf (4 * m) ^ 2 ≤ 4 * m := by
      have hp := rOf_pow_le (4 * m)
      have h3 : rOf (4 * m) ^ 2 ≤ rOf (4 * m) ^ 3 := by
        rcases Nat.eq_zero_or_pos (rOf (4 * m)) with h0 | hpos
        · simp [h0]
        · exact Nat.pow_le_pow_right hpos (by omega)
      have hl : Nat.log 2 (4 * m) ≤ 4 * m := by
        have := natLog2_add_one_le_self' (by omega : 1 ≤ 4 * m); omega
      omega
    have hc_phi_n : c_phi ≤ 120 * (7 * m + K_nat * (4 * m)) := by
      have : 4 * m + 2 + 4 ≤ 7 * m := by omega
      calc c_phi ≤ 120 * (Nat.log 2 (4 * m + 2) + K_nat * rOf (4 * m) ^ 2 + 4) := hc_phi
        _ ≤ 120 * ((4 * m + 2) + K_nat * (4 * m) + 4) := by gcongr
        _ ≤ 120 * (7 * m + K_nat * (4 * m)) := by omega
    have hcast : (c_phi : ℝ) ≤ 120 * (50 + 48 * ↑K_nat) * ↑m := by
      have hc_r : (c_phi : ℝ) ≤ 120 * (7 * ↑m + ↑K_nat * (4 * ↑m)) := by exact_mod_cast hc_phi_n
      have hkn_nn : (0 : ℝ) ≤ (K_nat : ℝ) := by exact_mod_cast (by omega : 0 ≤ K_nat)
      nlinarith
    calc (c_phi : ℝ) ≤ 120 * (50 + 48 * ↑K_nat) * ↑m * 1 := by linarith
      _ ≤ 120 * (50 + 48 * ↑K_nat) * ↑m * subpolyB1 (2 + C₀_lvl) m := by
        have hnn : 0 ≤ 120 * (50 + 48 * (K_nat : ℝ)) * (m : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hsb_cost hnn
  have hc_rest_lin : ((c_ell + c_lay + c_init + c_pack + 19 + 6 * (Nat.log 2 (m / n) + 1) + 4 : ℕ) : ℝ) ≤
      2000 * ↑m * subpolyB1 (2 + C₀_lvl) m := by
    have hlog2m : Nat.log 2 (2 * m + 1) + 1 ≤ 2 * m + 1 := natLog2_add_one_le_self' (by omega)
    have htot : c_ell + c_lay + c_init + c_pack + 19 + 6 * (Nat.log 2 (m / n) + 1) + 4 ≤ 1000 * m := by
      omega
    have hr : ((c_ell + c_lay + c_init + c_pack + 19 + 6 * (Nat.log 2 (m / n) + 1) + 4 : ℕ) : ℝ) ≤
        1000 * ↑m := by exact_mod_cast htot
    calc _ ≤ 2000 * ↑m * 1 := by linarith
      _ ≤ 2000 * ↑m * subpolyB1 (2 + C₀_lvl) m :=
        mul_le_mul_of_nonneg_left hsb_cost (by positivity)
  have h100_le : (100 : ℝ) ≤ 100 * ↑m * subpolyB1 C₀_lvl m := by nlinarith
  have hc_loop_main : ((Nat.log 2 (m / n) + 1 : ℕ) : ℝ) * (C_lvl * ↑m * subpolyB1 C₀_lvl m + 100) ≤
      13 * (C_lvl + 100) * ↑m * subpolyB1 (2 + C₀_lvl) m := by
    have hinner : C_lvl * ↑m * subpolyB1 C₀_lvl m + 100 ≤ (C_lvl + 100) * ↑m * subpolyB1 C₀_lvl m := by
      nlinarith
    have hnonneg : 0 ≤ (C_lvl + 100) * ↑m * subpolyB1 C₀_lvl m := by positivity
    have h1 := mul_le_mul hℓ_sb hinner (by positivity) (by positivity)
    have hmul : 13 * subpolyB1 2 m * ((C_lvl + 100) * ↑m * subpolyB1 C₀_lvl m) =
        13 * (C_lvl + 100) * ↑m * (subpolyB1 2 m * subpolyB1 C₀_lvl m) := by ring
    rw [hmul, subpolyB1_mul] at h1
    exact h1
  have hsum_all :
      ((c_phi + (c_ell + (c_lay + (c_init + (c_loop + c_pack + 1) + 1) + 1) + 1) + 1 + 14 : ℕ) : ℝ) ≤
        (13 * (C_lvl + 100) + 120 * (50 + 48 * ↑K_nat) + 2000) * (↑m * subpolyB1 (2 + C₀_lvl) m + 1) := by
    have hr1 : ((c_phi + (c_ell + (c_lay + (c_init + (c_loop + c_pack + 1) + 1) + 1) + 1) + 1 + 14 : ℕ) : ℝ) =
        (c_phi : ℝ) + (c_loop : ℝ) +
          ((c_ell + c_lay + c_init + c_pack + 19 : ℕ) : ℝ) := by
      push_cast; ring
    have hrest_part : ((c_ell + c_lay + c_init + c_pack + 19 : ℕ) : ℝ) +
        (6 * ↑(Nat.log 2 (m / n) + 1) + 4) =
        ((c_ell + c_lay + c_init + c_pack + 19 + 6 * (Nat.log 2 (m / n) + 1) + 4 : ℕ) : ℝ) := by
      push_cast; ring
    have hk_nn : 0 ≤ 13 * (C_lvl + 100) + 120 * (50 + 48 * (K_nat : ℝ)) + 2000 := by positivity
    linarith
  exact_mod_cast le_trans hsum_all (Nat.le_ceil _)

theorem decomposeEntry_spec_aux
    {K : ℝ} {cr : ℝ} {P : Program} {c : ℕ}
    (hK : 0 < K)
    (hDec : ∀ (G_tw : Cited.Graph), G_tw.IsValid → G_tw.IsLoopless → thresholdB1 cr ≤ G_tw.m →
      ∀ (ω : ℕ → Bool), ∃ out cost,
        RunsTo (wordSize c (G_tw.encode ++ [1, 200, rOf G_tw.m])) P
          (G_tw.encode ++ [1, 200, rOf G_tw.m]) ω out cost ∧
        IsExpanderDecomposition G_tw (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
          ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
            (K * Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2))) out ∧
        (cost : ℝ) ≤ K * (G_tw.n + ((G_tw.m : ℝ) + 2) ^ (1 + K / rOf G_tw.m) *
          Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2) /
            (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2))
    {K_nat thr C_phi : ℕ} {C₀_p C₁_p : ℝ}
    (hK_nat : K ≤ ↑K_nat) (hKn1 : 1 ≤ K_nat)
    (hthr200 : 200 ≤ thr) (hthr_cr : thresholdB1 cr ≤ thr)
    (hC₀p : 0 < C₀_p) (hC₁p : 1 ≤ C₁_p)
    (hphi_sb : ∀ m, (maxPhiDenOf K_nat thr m : ℝ) ≤ C₁_p * subpolyB1 C₀_p m)
    (hCphi_pos : 1 ≤ C_phi) (hCphi : ∀ m, maxPhiDenOf K_nat thr m ≤ C_phi * (m + 2) ^ 1) :
    let C₀_c : ℝ := 64 * ↑K_nat
    let C_c : ℝ := 40000 * 5 * ↑K_nat + 2 * ↑K_nat + 1
    let C₀_lvl : ℝ := max C₀_c (2 * C₀_p + 4)
    let C_lvl : ℝ := 2000 * (100 + ↑(runnerScale P) * (C_c + ↑c + 10) + 144 * 36 * (64 * C₁_p + 36) ^ 2)
    let C₀_cost : ℝ := 2 + C₀_lvl
    let K_dec : ℝ := 13 * (C_lvl + 100) + 120 * (50 + 48 * ↑K_nat) + 2000
    ∀ w p b, p.HasAt b (decomposeProcs K_nat thr P c b) →
      MeetsContract w p b
        (decomposeHeapContract 1 K_dec (subpolyB1 C₀_cost)
          (fun m => 1 / (maxPhiDenOf K_nat thr m : ℝ)) (maxPhiDenOf K_nat thr) 4
          (fun n m => decompSpace C_phi c n m) w) := by
  intro C₀_c C_c C₀_lvl C_lvl C₀_cost K_dec w p b hHas
  have hc := mkDecompProgContracts K_nat thr P c w b p hHas
  intro args mem₀ pos ω _ hpre
  rcases hpre with ⟨⟨gAddr, h, G, rfl, hGh, hga, hGv, hGl, hcw⟩, hzero0, hsp_w⟩
  change ZeroFrom mem₀ h at hzero0
  change h + decompSpace C_phi c (readGraph mem₀ gAddr).n (readGraph mem₀ gAddr).m < 2 ^ w at hsp_w
  rw [Spanner.graphAt_iff_readGraph.mp hga] at hsp_w
  set B := G.n + G.m + maxPhiDenOf K_nat thr G.m + 2
  have hB_ge : 605 ≤ B := by
    have h1 := le_phiDenHalf_thr K_nat thr G.m
    have h2 : maxPhiDenOf K_nat thr G.m = 3 * phiDenHalf K_nat thr G.m := rfl
    omega
  have hB4 : B ^ 4 < 2 ^ w := by
    have hlt : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by omega) B
    have hpow := Nat.pow_lt_pow_left hlt (by omega : 4 ≠ 0)
    have h4w : 4 * (Nat.log 2 B + 1) ≤ w := hcw
    calc B ^ 4 < (2 ^ (Nat.log 2 B + 1)) ^ 4 := hpow
      _ = 2 ^ (4 * (Nat.log 2 B + 1)) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) h4w
  have hB1 : B < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow (by omega : 4 ≠ 0) B) hB4
  have h1w : 1 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h20w : 20 ≤ 2 ^ w := by omega
  have hGenc_ge : 2 ≤ G.encode.length := by simp [Cited.Graph.encode]
  have hh_w : h < 2 ^ w := by
    have hgn2 : 2 ≤ G.n + G.m + 2 := by omega
    have h4sq : 4 ≤ (G.n + G.m + 2) ^ 2 := by rw [sq]; exact Nat.mul_le_mul hgn2 hgn2
    have h100 : 100 ≤ 100 + 64 * C_phi := by omega
    have h400 : 400 ≤ (100 + 64 * C_phi) * (G.n + G.m + 2) ^ 2 := Nat.mul_le_mul h100 h4sq
    have hc1 : 1 ≤ (416 * (G.n + G.m + 2)) ^ c := Nat.one_le_pow _ _ (by omega)
    have hm3a : 3 ≤ G.m + 3 := by omega
    have hm3b : 3 ≤ 1 + 2 * (416 * (G.n + G.m + 2)) ^ c := by omega
    have hm3 : 9 ≤ (G.m + 3) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) :=
      Nat.mul_le_mul hm3a hm3b
    have hds : 419 ≤ decompSpace C_phi c G.n G.m := by
      unfold decompSpace
      omega
    omega
  have hga0 : mem₀ gAddr = G.n := by
    have := hga 0 (by simp [Cited.Graph.encode])
    simpa [Cited.Graph.encode] using this
  have hga1 : mem₀ (gAddr + 1) = G.m := by
    have := hga 1 (by simp [Cited.Graph.encode])
    simpa [Cited.Graph.encode] using this
  let st₀ := startState [gAddr, h] mem₀ pos
  have hst0_g : st₀.regs rGAddr = gAddr := rfl
  have hst0_h : st₀.regs rOutH = h := rfl
  let stA : State := { st₀ with regs := Function.update st₀.regs rN G.n }
  have hstA_run : Runs w p ω (.assign rN (.load (.reg rGAddr))) st₀ .normal stA 3 := by
    apply runs_assign_iff.mpr
    refine ⟨G.n, dp_ev_load (dp_ev_reg hst0_g) hga0, rfl, rfl, by simp [Expr.size]⟩
  let stB : State := { stA with regs := Function.update stA.regs rM G.m }
  have hstA_g : stA.regs rGAddr = gAddr := by
    dsimp [stA]; rw [Function.update_of_ne (by decide)]; exact hst0_g
  have hstB_run : Runs w p ω (.assign rM (.load (.bin .add (.reg rGAddr) (.const 1)))) stA .normal stB 5 := by
    apply runs_assign_iff.mpr
    refine ⟨G.m, dp_ev_load (dp_ev_add (dp_ev_reg hstA_g) (dp_ev_const h1w) (by omega)) hga1,
      rfl, rfl, by simp [Expr.size]⟩
  have hstB_g : stB.regs rGAddr = gAddr := by dsimp [stB]; rw [Function.update_of_ne (by decide)]; exact hstA_g
  have hstB_h : stB.regs rOutH = h := by
    dsimp [stB, stA]; repeat rw [Function.update_of_ne (by decide)]; exact hst0_h
  have hstB_n : stB.regs rN = G.n := by
    dsimp [stB, stA]; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  have hstB_m : stB.regs rM = G.m := by dsimp [stB]; exact Function.update_self _ _ _
  have hlt_ev : Expr.eval w stB (.bin .lt (.reg rN) (.reg rM)) = some (if G.n < G.m then 1 else 0) :=
    dp_ev_lt (dp_ev_reg hstB_n) (dp_ev_reg hstB_m) h1w
  refine ⟨decomposeEntry K_nat thr (b + 11), hc.hEntry, ?_⟩
  by_cases hnm : G.n < G.m
  · have h1n : 1 ≤ G.n := one_le_n_of_lt hGv hnm
    have h4B_le_B4 : 4 * B ≤ B ^ 4 := by
      calc 4 * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
        _ = B ^ 2 := (sq B).symm
        _ ≤ B ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h4m2_w : 4 * G.m + 2 < 2 ^ w := by omega
    have hlog4m2_w : (Nat.log 2 (4 * G.m + 2) + 2) ^ 3 < 2 ^ w := by
      have h1 : Nat.log 2 (4 * G.m + 2) ≤ 4 * G.m + 2 := by
        have := natLog2_add_one_le_self' (by omega : 1 ≤ 4 * G.m + 2); omega
      have h2 : Nat.log 2 (4 * G.m + 2) + 2 ≤ 4 * B := by omega
      have h3 : (Nat.log 2 (4 * G.m + 2) + 2) ^ 3 ≤ 64 * B ^ 3 := by
        have hp := Nat.pow_le_pow_left h2 3
        simpa [mul_pow] using hp
      have h64 : 64 * B ^ 3 ≤ B ^ 4 := by
        have h64B : 64 ≤ B := by omega
        calc 64 * B ^ 3 ≤ B * B ^ 3 := Nat.mul_le_mul_right (B ^ 3) h64B
          _ = B ^ 4 := by ring
      omega
    have hphi_w : phiDenHalf K_nat thr G.m < 2 ^ w := by
      have : maxPhiDenOf K_nat thr G.m = 3 * phiDenHalf K_nat thr G.m := rfl
      omega
    obtain ⟨o_p, stC, c_phi, hstC_run, hstC_post, hc_phi⟩ :=
      computePhiDenStmt_triple (w := w) (p := p) (K_nat := K_nat) (thr := thr) (m := G.m)
        hKn1 (rM := rM) (rOut := rDphi) (rL := rTmp1) (rR := rTmp2) (rPow := rTmp3)
        (rIdx := rTmp4) (rCur := rTmp5) (by decide) stB hstB_m h4m2_w hlog4m2_w hphi_w stB ω rfl
    cases o_p with
    | returned _ => exact False.elim hstC_post
    | normal =>
    rcases hstC_post with ⟨hstC_dphi, hstC_mem, hstC_pos, hstC_regs⟩
    have hstC_g : stC.regs rGAddr = gAddr := by rw [hstC_regs rGAddr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hstB_g
    have hstC_h : stC.regs rOutH = h := by rw [hstC_regs rOutH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hstB_h
    have hstC_n : stC.regs rN = G.n := by rw [hstC_regs rN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hstB_n
    have hstC_m : stC.regs rM = G.m := by rw [hstC_regs rM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hstB_m
    obtain ⟨stD, c_ell, hstD_run, hstD_ell, hstD_mem, hstD_pos, hstD_regs, hc_ell⟩ :=
      computeEll_runs (w := w) (p := p) (ω := ω) G.n G.m h1n hnm (by omega) (by omega) stC hstC_n hstC_m
    have hstD_g : stD.regs rGAddr = gAddr := by rw [hstD_regs rGAddr (by decide) (by decide) (by decide)]; exact hstC_g
    have hstD_h : stD.regs rOutH = h := by rw [hstD_regs rOutH (by decide) (by decide) (by decide)]; exact hstC_h
    have hstD_n : stD.regs rN = G.n := by rw [hstD_regs rN (by decide) (by decide) (by decide)]; exact hstC_n
    have hstD_m : stD.regs rM = G.m := by rw [hstD_regs rM (by decide) (by decide) (by decide)]; exact hstC_m
    have hstD_dp : stD.regs rDphi = phiDenHalf K_nat thr G.m := by
      rw [hstD_regs rDphi (by decide) (by decide) (by decide)]; exact hstC_dphi
    set ℓ := Nat.log 2 (G.m / G.n) + 1
    set D_phi := phiDenHalf K_nat thr G.m
    set L := mkDecompLayout h G.n G.m D_phi
    have hb := mkDecompLayout_bounds h G.n G.m D_phi
    change DecompLayoutBounds L h G.n G.m D_phi at hb
    rcases hb with ⟨hL_sp, hL_bnd, hL_lvl, hL_g0, hL_i0, hL_g1, hL_i1, hL_tw, hL_buf, hL_work, hL_kept, hL_ar, hL_zc⟩
    have h2pow_ell_n : 2 ^ ℓ * G.n ≤ 2 * G.m := two_pow_ell_mul_n_le h1n hnm
    have h2pow_ell : 2 ^ ℓ ≤ 2 * G.m := le_trans (Nat.le_mul_of_pos_right (2 ^ ℓ) h1n) h2pow_ell_n
    have hL_zc_le : L.zeroCursor₀ - h ≤ (100 + 64 * C_phi) * (G.n + G.m + 2) ^ 2 := by
      apply layout_zeroCursor_le
      have : D_phi ≤ maxPhiDenOf K_nat thr G.m := by change D_phi ≤ 3 * D_phi; omega
      exact le_trans this (by simpa only [pow_one] using hCphi G.m)
    have hL_zc_lt : L.zeroCursor₀ < 2 ^ w := by
      have : L.zeroCursor₀ ≤ h + decompSpace C_phi c G.n G.m := by
        unfold decompSpace; omega
      omega
    obtain ⟨stE, c_lay, hstE_run, hstE_regs, hstE_mem, hstE_pos, hc_lay⟩ :=
      computeLayout_runs (w := w) (p := p) (ω := ω) gAddr h G.n G.m ℓ D_phi h1n hnm h2pow_ell
        hL_zc_lt h20w stD hstD_g hstD_h hstD_n hstD_m hstD_ell hstD_dp
    have hstE_mem0 : stE.mem = mem₀ := by rw [hstE_mem, hstD_mem, hstC_mem]; rfl
    have hga_E : GraphAt stE.mem gAddr G := hstE_mem0 ▸ hga
    obtain ⟨stF, c_init, hstF_run, hstF_regs, hstF_sp, hstF_zc, hstF_tot, hstF_g0, hstF_i0,
        hstF_fr1, hstF_fr2, hstF_fr3, hstF_pos, hc_init⟩ :=
      initMemory_runs (w := w) (p := p) (ω := ω) gAddr h ℓ D_phi G stE hGh hga_E hL_zc_lt
        (by omega) hstE_regs
    have hzero_F : ZeroFrom stF.mem L.zeroCursor₀ := by
      intro a ha
      have hle_i0 : L.idx0Addr + G.m ≤ a := by omega
      rw [hstF_fr3 a hle_i0, hstE_mem0]
      exact hzero0 a (by omega)
    have hGm_pow : G.m ≤ 2 ^ ℓ * G.n := by
      have hlt : G.m / G.n < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by omega) (G.m / G.n)
      have hmod := Nat.div_add_mod G.m G.n
      rw [Nat.mul_comm G.n (G.m / G.n)] at hmod
      have hm1 : G.m % G.n < G.n := Nat.mod_lt G.m h1n
      have hdiv_le : G.m / G.n + 1 ≤ 2 ^ ℓ := hlt
      have hmul_le : (G.m / G.n + 1) * G.n ≤ 2 ^ ℓ * G.n := Nat.mul_le_mul_right G.n hdiv_le
      rw [Nat.succ_mul] at hmul_le
      omega
    have hca0 : curAddrs L (ℓ - ℓ) = (L.g0Addr, L.idx0Addr, L.g1Addr, L.idx1Addr) := by
      simp [curAddrs]
    have hinv_init : DecompLoopInv G gAddr h ℓ D_phi c ℓ mem₀ [] G (List.range G.m)
        L.arena₀ L.zeroCursor₀ stF := by
      refine
        { hk := le_rfl
          hlen := by simp
          hregs := by dsimp only; rw [hca0]; exact hstF_regs
          hrem_valid := hGv
          hrem_loopless := hGl
          hrem_n := rfl
          hrem_m_le_pow := hGm_pow
          hrem_m_le := le_rfl
          hrem_edges := by
            apply List.ext_getElem
            · simp [Cited.Graph.m]
            · intro i hi1 hi2
              simp [List.getD, hi1]
          hidx_len := List.length_range
          hidx_pw := by
            have : ∀ k : ℕ, (List.range k).Pairwise (· < ·) := by
              intro k; induction k with
              | zero => simp
              | succ k ih =>
                rw [List.range_succ]
                exact List.pairwise_append.mpr ⟨ih, by simp, fun a ha b hb => by simp at ha hb; omega⟩
            exact this G.m
          hidx_lt := fun a ha => List.mem_range.mp ha
          hcurG_at := by rw [hca0]; exact hstF_g0
          hcurIdx_at := by rw [hca0]; exact hstF_i0
          hstate_ar := hstF_sp
          hstate_zc := hstF_zc
          hstate_tot := hstF_tot
          hzero := hzero_F
          harena_ge := le_rfl
          harena_m := rfl.le
          htotal_m := by simp
          hzc_ge := le_rfl
          hzc_le := by simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]; exact le_rfl
          hrecs := fun _ hi => by simp at hi
          hbounds := fun _ hi => by simp at hi
          hlvl := fun a ha => by
            have hb1 : L.boundsAddr ≤ L.lvlArrAddr + a := by omega
            have hb2 : L.lvlArrAddr + a < L.g0Addr := by omega
            have h0 : stF.mem (L.lvlArrAddr + a) = 0 := by
              rw [hstF_fr2 _ hb1 hb2, hstE_mem0]
              exact hzero0 _ (by omega)
            refine ⟨⟨fun _ => List.mem_range.mpr ha, fun _ => h0⟩,
              fun _ hi => by simp at hi, Or.inl h0⟩
          hframe := fun a ha => by
            have hlt_sp : a < L.statePtr := by omega
            rw [hstF_fr1 a hlt_sp, hstE_mem0] }
    let c_cited_ub := ⌈(40000 * 5 * ↑K_nat + 2 * ↑K_nat : ℝ) * ↑G.m * subpolyB1 (64 * ↑K_nat) G.m⌉₊
    let c_ws_ub := 5 * c * (Nat.log 2 (G.n + G.m + 206) + 1)
    have hcited_ub_def : ∀ (m_tw : ℕ), 200 ≤ m_tw → m_tw ≤ 4 * G.m →
        K * (2 * ↑G.n + (↑m_tw + 2) ^ (1 + K / ↑(rOf m_tw)) *
          Real.log (↑m_tw + 2) ^ (K * ↑(rOf m_tw) ^ 2) / (1 / 200 : ℝ) ^ 2) ≤ ↑c_cited_ub := by
      intro m_tw hm200 hm_4m
      have hcb := citedCost_le_mul_subpoly hK hK_nat (by omega : 1 ≤ G.m) hnm hm200 hm_4m
      exact le_trans hcb (Nat.le_ceil _)
    have hlevel_ub : ∀ (curM D : ℕ), curM ≤ G.m → D * G.n ≤ 2 * G.m →
        ∀ (cw_s : ℕ), cw_s ≤ c_ws_ub →
          ↑(levelCost G.n curM D D_phi c_cited_ub (runnerScale P) cw_s) ≤
            C_lvl * ↑G.m * subpolyB1 C₀_lvl G.m := by
      intro curM D hcurM hDn cw_s hcw_s
      have hDphi_sb : (D_phi : ℝ) ≤ C₁_p * subpolyB1 C₀_p G.m := by
        have h1 : (D_phi : ℝ) ≤ (maxPhiDenOf K_nat thr G.m : ℝ) := by
          exact_mod_cast (by change D_phi ≤ 3 * D_phi; omega : D_phi ≤ maxPhiDenOf K_nat thr G.m)
        exact le_trans h1 (hphi_sb G.m)
      have hc_cited_sb : (c_cited_ub : ℝ) ≤ C_c * ↑G.m * subpolyB1 C₀_c G.m := by
        have hsb_c : (1 : ℝ) ≤ subpolyB1 (64 * ↑K_nat) G.m := one_le_subpolyB1 (by positivity) G.m
        have hm_r : (1 : ℝ) ≤ ↑G.m := by exact_mod_cast (by omega : 1 ≤ G.m)
        have h1 : (c_cited_ub : ℝ) < (40000 * 5 * ↑K_nat + 2 * ↑K_nat : ℝ) * ↑G.m * subpolyB1 (64 * ↑K_nat) G.m + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have h1_le : (1 : ℝ) ≤ ↑G.m * subpolyB1 (64 * ↑K_nat) G.m := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ ↑G.m * subpolyB1 (64 * ↑K_nat) G.m := mul_le_mul hm_r hsb_c zero_le_one (by positivity)
        dsimp only [C_c, C₀_c]
        have hexp : (40000 * 5 * ↑K_nat + 2 * ↑K_nat + 1 : ℝ) * ↑G.m * subpolyB1 (64 * ↑K_nat) G.m =
            (40000 * 5 * ↑K_nat + 2 * ↑K_nat : ℝ) * ↑G.m * subpolyB1 (64 * ↑K_nat) G.m +
              ↑G.m * subpolyB1 (64 * ↑K_nat) G.m := by ring
        linarith
      exact levelCost_le_subpoly hC₀p.le hC₁p (by positivity) (by
        dsimp only [C_c]
        have h0 : (0 : ℝ) ≤ ↑K_nat := Nat.cast_nonneg _
        linarith)
        (by omega) hnm hcurM hDn hDphi_sb hc_cited_sb hcw_s
    have hc_ws_spec : ∀ (D : ℕ) (curG : Cited.Graph), curG.IsValid → curG.m ≤ G.m → D * G.n ≤ 2 * G.m →
        curG.n = G.n →
          2 ^ (wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) + 1) ≤
            2 * (416 * (G.n + G.m + 2)) ^ c ∧
          wordSize c ((twinGraph D curG).encode ++ [1, 200, rOf (curG.m + D * curG.n)]) ≤ c_ws_ub := by
      intro D curG hV hm_le hDn hn_eq
      exact two_pow_wordSize_twin_le hV c G.n G.m hn_eq hnm hm_le hDn
    obtain ⟨recs, remG, remIdx, arena_f, zc_f, stG, c_loop, hstG_run, hinvG, hc_loop⟩ :=
      decomposeLevelLoop_runs hK hDec hK_nat hthr200 hthr_cr hc G gAddr h ℓ C₀_lvl C_lvl
        c_cited_ub c_ws_ub h1n hnm rfl (hCphi G.m) hsp_w hB4 hcited_ub_def hlevel_ub hc_ws_spec
        mem₀ ℓ [] G (List.range G.m) L.arena₀ L.zeroCursor₀ stF hinv_init
    let level : List ℕ := List.ofFn (fun i : Fin G.m => stG.mem (L.lvlArrAddr + i))
    have hlvl_len : level.length = G.m := List.length_ofFn
    have hlvl_at : ListAt stG.mem L.lvlArrAddr level := by
      intro idx hidx
      have hi : idx < G.m := hlvl_len ▸ hidx
      simp [level, List.getElem_ofFn]
    have hpart0 : ∀ a < G.m,
        (level.getD a 0 = 0 ↔ a ∈ remIdx) ∧
        (∀ (t : ℕ) (ht : t < recs.length), level.getD a 0 = t + 1 ↔ a ∈ recs[t].keptIdx) ∧
        (level.getD a 0 = 0 ∨ ∃ t, ∃ (_ : t < recs.length), level.getD a 0 = t + 1) := by
      intro a ha
      have ha_lvl : a < level.length := hlvl_len.symm ▸ ha
      have hget : level.getD a 0 = stG.mem (L.lvlArrAddr + a) := by
        simp [List.getD, List.getElem?_eq_getElem ha_lvl, level, List.getElem_ofFn]
      rw [hget]
      simpa using hinvG.hlvl a ha
    have hrecs0 : ∀ (t : ℕ) (ht : t < recs.length),
        recs[t].lvl = t + 1 ∧
        (∀ comp ∈ recs[t].rawComps, comp.1 = t + 1 ∧ List.Pairwise (· < ·) comp.2 ∧ 2 ≤ comp.2.length) ∧
        List.map (fun c => c.2.toFinset) recs[t].rawComps = recs[t].validRs ∧
        List.Pairwise (· < ·) recs[t].keptIdx ∧
        (∀ a ∈ recs[t].keptIdx, a < G.m) ∧
        recs[t].Gi.n = G.n ∧
        recs[t].Gi.edges = List.map (fun j => G.edges.getD j (0, 0)) recs[t].keptIdx ∧
        recs[t].Gi.m ≤ 2 ^ (t + 1) * G.n ∧
        List.Pairwise Disjoint recs[t].validRs ∧
        (∀ R ∈ recs[t].validRs, R ⊆ G.verts ∧ 2 ≤ R.card ∧
          recs[t].Gi.IsConductanceExpanderOn R ((1 : ℝ) / (3 * (D_phi : ℝ))) ∧
          (∀ x ∈ R, (1 : ℝ) / (3 * (D_phi : ℝ)) * 2 ^ (t + 1) ≤ ↑(recs[t].Gi.degIn R x)) ∧
          ∀ e ∈ recs[t].Gi.edges, e.1 ∈ R ↔ e.2 ∈ R) ∧
        ∀ e ∈ recs[t].Gi.edges, ∃ R ∈ recs[t].validRs, e.1 ∈ R ∧ e.2 ∈ R := by
      intro t ht
      simpa only [Nat.zero_add] using hinvG.hrecs t ht
    have hrem_m0 : remG.m ≤ G.n := by simpa using hinvG.hrem_m_le_pow
    obtain ⟨hraw_pw, hraw_bds, hdecomp_prop⟩ :=
      decompProp_of_multiLevel h1n hnm (φ := (1 : ℝ) / (3 * (D_phi : ℝ)))
        recs remG remIdx level ℓ rfl hinvG.hlen hinvG.hrem_n
        hrem_m0 hinvG.hrem_edges hinvG.hidx_pw hinvG.hidx_lt hlvl_len hrecs0 hpart0
    set rawComps := (recs.map (fun x => x.rawComps)).flatten
    have hdp_ge1 : 1 ≤ 3 * D_phi := by have := le_phiDenHalf_thr K_nat thr G.m; omega
    have hdecomp_prop' : Spanner.DecomposeProp 1 G (Spanner.mkDecomposeOutput ℓ level rawComps)
        ((↑(1 : ℕ) : ℝ) / ↑(3 * D_phi)) := by
      rwa [show ((↑(1 : ℕ) : ℝ) / ↑(3 * D_phi)) = (1 : ℝ) / (3 * (D_phi : ℝ)) by push_cast; rfl]
    have henc_len : (Spanner.Decompose.encode ℓ 1 (3 * D_phi) level rawComps).length ≤ 4 + 5 * G.m :=
      decompose_encode_length_le_five_mul_m hlvl_len le_rfl hdp_ge1 hraw_pw hraw_bds hdecomp_prop'
    have hℓ_le_m : ℓ ≤ G.m :=
      le_trans (natLog2_add_one_le_self' (Nat.div_pos (le_of_lt hnm) h1n)) (Nat.div_le_self G.m G.n)
    have hℓ_le_m2 : ℓ ≤ G.m + 2 := by omega
    have hzc_f_ub : zc_f ≤ h + decompSpace C_phi c G.n G.m := by
      have hl_le : ℓ ≤ G.m + 1 := by omega
      have hds_all : L.zeroCursor₀ + (G.m + 1) * (1 + (416 * (G.n + G.m + 2)) ^ c) ≤
          h + decompSpace C_phi c G.n G.m := by
        unfold decompSpace
        have hmul : (G.m + 1) * (1 + (416 * (G.n + G.m + 2)) ^ c) ≤
            (G.m + 3) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) := by
          have h1 : 1 + (416 * (G.n + G.m + 2)) ^ c ≤ 1 + 2 * (416 * (G.n + G.m + 2)) ^ c := by omega
          exact Nat.mul_le_mul (by omega) h1
        omega
      have hmul_done : (ℓ - 0) * (1 + (416 * (G.n + G.m + 2)) ^ c) ≤
          (G.m + 1) * (1 + (416 * (G.n + G.m + 2)) ^ c) :=
        Nat.mul_le_mul_right _ (by omega)
      have hzc_le' : zc_f ≤ L.zeroCursor₀ + (ℓ - 0) * (1 + (416 * (G.n + G.m + 2)) ^ c) := hinvG.hzc_le
      omega
    have hbounds0 : ∀ (t : ℕ) (ht : t < recs.length),
        let a0 := stG.mem (L.boundsAddr + 2 * (t + 1))
        let a1 := stG.mem (L.boundsAddr + 2 * (t + 1) + 1)
        L.arena₀ ≤ a0 ∧ a0 ≤ a1 ∧ a1 ≤ L.arena₀ + 4 * G.m ∧
          a1 - a0 = (List.flatMap compRecord recs[t].rawComps).length ∧
          ListAt stG.mem a0 (List.flatMap compRecord recs[t].rawComps) := by
      intro t ht
      have hb := hinvG.hbounds t ht
      simp only [Nat.zero_add] at hb
      have har_le : arena_f ≤ L.arena₀ + 4 * G.m := by
        have : arena_f + 4 * remG.m ≤ L.arena₀ + 4 * G.m := hinvG.harena_m
        omega
      exact ⟨hb.1, hb.2.1, le_trans hb.2.2.1 har_le, hb.2.2.2.1, hb.2.2.2.2⟩
    have hregs0 : DecompRegs gAddr h G.n G.m ℓ D_phi 0 (2 ^ 0)
        (curAddrs L ℓ).1 (curAddrs L ℓ).2.1 (curAddrs L ℓ).2.2.1 (curAddrs L ℓ).2.2.2 L stG := by
      simpa using hinvG.hregs
    have h3dp_eq : 3 * D_phi = maxPhiDenOf K_nat thr G.m := rfl
    obtain ⟨stH, c_pack, hstH_run, hout_at, hfr_pack, hc_pack⟩ :=
      packOutput_runs (w := w) (p := p) (ω := ω) gAddr h G.n G.m ℓ D_phi
        (curAddrs L ℓ).1 (curAddrs L ℓ).2.1
        (curAddrs L ℓ).2.2.1 (curAddrs L ℓ).2.2.2 zc_f recs level stG
        h1n hnm hℓ_le_m2 (by simpa using hinvG.hlen) hlvl_len hlvl_at hinvG.hstate_tot
        hinvG.hstate_zc hinvG.hzc_ge hbounds0 henc_len h4w (by omega) (by omega) hregs0
    have hseq_then := runs_seq hstC_run (runs_seq hstD_run (runs_seq hstE_run
      (runs_seq hstF_run (runs_seq hstG_run hstH_run))))
    have hcond_run : Runs w p ω
        (.cond (.bin .lt (.reg rN) (.reg rM))
          (seqStmts
            [ computePhiDenStmt K_nat thr rM rDphi rTmp1 rTmp2 rTmp3 rTmp4 rTmp5
            , computeEllStmt
            , computeLayoutStmt
            , initMemoryStmt
            , decomposeLevelLoop (b + 11)
            , packOutputStmt ])
          sparseFastPathStmt)
        stB (.returned zc_f) stH
          (3 + (c_phi + (c_ell + (c_lay + (c_init + (c_loop + c_pack + 1) + 1) + 1) + 1) + 1) + 1) := by
      refine runs_cond_iff.mpr ⟨1, _, by simp [hnm] at hlt_ev; exact hlt_ev, ?_, rfl⟩
      simpa [ite_false] using hseq_then
    have hfull_run := runs_seq hstA_run (runs_seq hstB_run hcond_run)
    change Runs w p ω (decomposeEntry K_nat thr (b + 11)) st₀ (.returned zc_f) stH _ at hfull_run
    refine ⟨.returned zc_f, stH, _, hfull_run, ?_, ?_⟩
    · have hzc_ge_L : L.zeroCursor₀ ≤ zc_f := hinvG.hzc_ge
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ℓ, 1, 3 * D_phi, level, rawComps, hout_at, ?_⟩
      · have : h ≤ L.zeroCursor₀ := by omega
        exact le_trans this hzc_ge_L
      · dsimp only [Outcome.value, heapArg, List.getLastD, List.getLast_cons, List.getLast_singleton,
          List.getD, List.getElem?_cons_zero, Option.getD_some]
        change zc_f ≤ h + decompSpace C_phi c (readGraph mem₀ gAddr).n (readGraph mem₀ gAddr).m
        rw [Spanner.graphAt_iff_readGraph.mp hga]
        exact hzc_f_ub
      · intro x hx
        rw [hfr_pack x (Or.inl hx)]
        exact hinvG.hframe x hx
      · intro a ha
        change zc_f ≤ a at ha
        have hsp_le : L.statePtr ≤ a := by
          have : L.statePtr ≤ L.zeroCursor₀ := by omega
          omega
        rw [hfr_pack a (Or.inr hsp_le)]
        exact hinvG.hzero a ha
      · refine ⟨gAddr, h, G, ℓ, 1, 3 * D_phi, level, rawComps, rfl, hga, hout_at, hlvl_len,
          le_rfl, hdp_ge1, le_rfl, (by dsimp only; rw [← h3dp_eq]; push_cast; exact le_rfl), hraw_pw, hraw_bds, ?_⟩
        simpa only [Nat.cast_one] using hdecomp_prop'
      · have hsp_eq : h + 4 + 5 * G.m = L.statePtr := rfl
        have hsp_zc : L.statePtr ≤ L.zeroCursor₀ := by omega
        refine ⟨?_, ?_⟩
        · change level.length = (readGraph mem₀ gAddr).m
          rw [Spanner.graphAt_iff_readGraph.mp hga]; exact hlvl_len
        change h + (Spanner.Decompose.encode ℓ 1 (3 * D_phi) level rawComps).length ≤ zc_f
        omega
    · have hC₀_nn : 0 ≤ C₀_lvl := le_trans (by positivity : (0 : ℝ) ≤ 64 * ↑K_nat) (le_max_left _ _)
      have hC_lvl_nn : 0 ≤ C_lvl := by dsimp only [C_lvl]; positivity
      have hc_eq : 3 + (5 + (3 + (c_phi + (c_ell + (c_lay + (c_init + (c_loop + c_pack + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 =
          c_phi + (c_ell + (c_lay + (c_init + (c_loop + c_pack + 1) + 1) + 1) + 1) + 1 + 14 := by ring
      rw [hc_eq]
      change _ ≤ ⌈K_dec * (↑(readGraph mem₀ gAddr).m * subpolyB1 C₀_cost (readGraph mem₀ gAddr).m + 1)⌉₊
      rw [Spanner.graphAt_iff_readGraph.mp hga]
      exact entry_cost_subpoly_le hC₀_nn hKn1 h1n hnm hC_lvl_nn
        hc_phi hc_ell hc_lay hc_init (by simpa [ℓ] using hc_loop) hc_pack
  · have hmn : G.m ≤ G.n := by omega
    have hm_ds : G.m + 4 ≤ decompSpace C_phi c G.n G.m := by
      have h1 : 1 ≤ (416 * (G.n + G.m + 2)) ^ c := Nat.one_le_pow _ _ (by omega)
      have hm3 : G.m + 3 ≤ (G.m + 3) * (1 + 2 * (416 * (G.n + G.m + 2)) ^ c) :=
        Nat.le_mul_of_pos_right _ (by omega)
      unfold decompSpace
      omega
    have hm_n_w : h + G.m + 4 < 2 ^ w := by omega
    obtain ⟨stF, c_fast, hstF_run, hout_at, hfr_fast, hc_fast⟩ :=
      sparseFastPath_runs (w := w) (p := p) (ω := ω) h G.m stB hstB_h hstB_m h4w hm_n_w
    have hcond_run : Runs w p ω
        (.cond (.bin .lt (.reg rN) (.reg rM))
          (seqStmts
            [ computePhiDenStmt K_nat thr rM rDphi rTmp1 rTmp2 rTmp3 rTmp4 rTmp5
            , computeEllStmt
            , computeLayoutStmt
            , initMemoryStmt
            , decomposeLevelLoop (b + 11)
            , packOutputStmt ])
          sparseFastPathStmt)
        stB (.returned (h + G.m + 4)) stF (3 + c_fast + 1) := by
      refine runs_cond_iff.mpr ⟨0, _, by simp [hnm] at hlt_ev; exact hlt_ev, ?_, rfl⟩
      simpa using hstF_run
    have hfull_run := runs_seq hstA_run (runs_seq hstB_run hcond_run)
    change Runs w p ω (decomposeEntry K_nat thr (b + 11)) st₀ (.returned (h + G.m + 4)) stF _ at hfull_run
    refine ⟨.returned (h + G.m + 4), stF, _, hfull_run, ?_, ?_⟩
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, 0, 1, 1, List.replicate G.m 0, [], hout_at, ?_⟩
      · change h ≤ h + G.m + 4; omega
      · dsimp only [Outcome.value, heapArg, List.getLastD, List.getLast_cons, List.getLast_singleton,
          List.getD, List.getElem?_cons_zero, Option.getD_some]
        change h + G.m + 4 ≤ h + decompSpace C_phi c (readGraph mem₀ gAddr).n (readGraph mem₀ gAddr).m
        rw [Spanner.graphAt_iff_readGraph.mp hga]
        omega
      · intro x hx
        exact hfr_fast x (Or.inl hx)
      · intro a ha
        change h + G.m + 4 ≤ a at ha
        rw [hfr_fast a (Or.inr ha)]
        exact hzero0 a (by omega)
      · refine ⟨gAddr, h, G, 0, 1, 1, List.replicate G.m 0, [], rfl, hga, hout_at,
          List.length_replicate, le_rfl, le_rfl, maxPhiDenOf_pos K_nat thr G.m, ?_,
          List.Pairwise.nil, fun _ hc' => by simp at hc', ?_⟩
        · have hm_pos : (1 : ℝ) ≤ ↑(maxPhiDenOf K_nat thr G.m) := by
            exact_mod_cast maxPhiDenOf_pos K_nat thr G.m
          push_cast; rw [div_one]; exact div_le_one_of_le₀ hm_pos (by positivity)
        · simpa using decomposeProp_zero_of_le G hmn
      · have henc : (Spanner.Decompose.encode 0 1 1 (List.replicate G.m 0) []).length = G.m + 4 := by
          simp [Spanner.Decompose.encode]
        refine ⟨?_, ?_⟩
        · change (List.replicate G.m 0).length = (readGraph mem₀ gAddr).m
          rw [Spanner.graphAt_iff_readGraph.mp hga]; exact List.length_replicate
        change h + (Spanner.Decompose.encode 0 1 1 (List.replicate G.m 0) []).length ≤ h + G.m + 4
        rw [henc]; omega
    · have hc_tot : 3 + (5 + (3 + c_fast + 1) + 1) + 1 ≤ 18 * G.m + 69 := by omega
      have hC₀_cost_nn : 0 ≤ C₀_cost := by
        dsimp only [C₀_cost, C₀_lvl, C₀_c]; positivity
      have hsb1 : (1 : ℝ) ≤ subpolyB1 C₀_cost G.m := one_le_subpolyB1 hC₀_cost_nn G.m
      have hk_ge : (2000 : ℝ) ≤ K_dec := by
        have hC_lvl_nn : 0 ≤ C_lvl := by dsimp only [C_lvl, C_c]; positivity
        have hK_nn : (0 : ℝ) ≤ ↑K_nat := Nat.cast_nonneg _
        dsimp only [K_dec]
        linarith
      have hc_real : ((3 + (5 + (3 + c_fast + 1) + 1) + 1 : ℕ) : ℝ) ≤
          K_dec * (↑G.m * subpolyB1 C₀_cost G.m + 1) := by
        have hm_nn : (0 : ℝ) ≤ ↑G.m := Nat.cast_nonneg _
        have h1 : ((3 + (5 + (3 + c_fast + 1) + 1) + 1 : ℕ) : ℝ) ≤ 18 * ↑G.m + 69 := by
          exact_mod_cast hc_tot
        have h2 : 18 * ↑G.m + 69 ≤ 2000 * (↑G.m * subpolyB1 C₀_cost G.m + 1) := by
          have h3 : (↑G.m : ℝ) ≤ ↑G.m * subpolyB1 C₀_cost G.m := le_mul_of_one_le_right hm_nn hsb1
          linarith
        have h4 : 2000 * (↑G.m * subpolyB1 C₀_cost G.m + 1) ≤
            K_dec * (↑G.m * subpolyB1 C₀_cost G.m + 1) :=
          mul_le_mul_of_nonneg_right hk_ge (by positivity)
        linarith
      change _ ≤ ⌈K_dec * (↑(readGraph mem₀ gAddr).m * subpolyB1 C₀_cost (readGraph mem₀ gAddr).m + 1)⌉₊
      rw [Spanner.graphAt_iff_readGraph.mp hga]
      exact_mod_cast le_trans hc_real (Nat.le_ceil _)

@[expose] noncomputable def mkDecomposeImplAux
    (K cr : ℝ) (P : Program) (c K_nat thr C_phi : ℕ) (C₀_p C₁_p : ℝ)
    (hK : 0 < K)
    (hDec : ∀ (G_tw : Cited.Graph), G_tw.IsValid → G_tw.IsLoopless → thresholdB1 cr ≤ G_tw.m →
      ∀ (ω : ℕ → Bool), ∃ out cost,
        RunsTo (wordSize c (G_tw.encode ++ [1, 200, rOf G_tw.m])) P
          (G_tw.encode ++ [1, 200, rOf G_tw.m]) ω out cost ∧
        IsExpanderDecomposition G_tw (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
          ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
            (K * Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2))) out ∧
        (cost : ℝ) ≤ K * (G_tw.n + ((G_tw.m : ℝ) + 2) ^ (1 + K / rOf G_tw.m) *
          Real.log ((G_tw.m : ℝ) + 2) ^ (K * (rOf G_tw.m : ℝ) ^ 2) /
            (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2))
    (hK_nat : K ≤ ↑K_nat) (hKn1 : 1 ≤ K_nat)
    (hthr200 : 200 ≤ thr) (hthr_cr : thresholdB1 cr ≤ thr)
    (hC₀p : 0 < C₀_p) (hC₁p : 1 ≤ C₁_p)
    (hphi_sb : ∀ m, (maxPhiDenOf K_nat thr m : ℝ) ≤ C₁_p * subpolyB1 C₀_p m)
    (hCphi_pos : 1 ≤ C_phi) (hCphi : ∀ m, maxPhiDenOf K_nat thr m ≤ C_phi * (m + 2) ^ 1) :
    Spanner.DecomposeImpl :=
  let C₀_c : ℝ := 64 * ↑K_nat
  let C_c : ℝ := 40000 * 5 * ↑K_nat + 2 * ↑K_nat + 1
  let C₀_lvl : ℝ := max C₀_c (2 * C₀_p + 4)
  let C_lvl : ℝ := 2000 * (100 + ↑(runnerScale P) * (C_c + ↑c + 10) + 144 * 36 * (64 * C₁_p + 36) ^ 2)
  let C₀_cost : ℝ := 2 + C₀_lvl
  let K_dec : ℝ := 13 * (C_lvl + 100) + 120 * (50 + 48 * ↑K_nat) + 2000
  let C₀_nn : 0 ≤ C₀_cost := by dsimp only [C₀_cost, C₀_lvl, C₀_c]; positivity
  Spanner.DecomposeImpl.mk
    (c_ℓ := 1)
    (K_dec := K_dec)
    (decFactor := subpolyB1 C₀_cost)
    (φ_lb := fun m => 1 / (maxPhiDenOf K_nat thr m : ℝ))
    (maxPhiDen := maxPhiDenOf K_nat thr)
    (C_phi := C_phi)
    (c_phi := 1)
    (cw := 4)
    (space := fun n m => decompSpace C_phi c n m)
    (C_space := 100 + 64 * C_phi + 12 + 4 * 416 ^ c)
    (c_space := max 2 (c + 1))
    (hc_ℓ := le_rfl)
    (hK_dec := by dsimp only [K_dec, C_lvl, C_c]; positivity)
    (hdec_ge := fun m => one_le_subpolyB1 C₀_nn m)
    (hdec_mono := fun _ _ hle => subpolyB1_mono_m C₀_nn hle)
    (hφ_lb_pos := fun m => by
      have hm : (0 : ℝ) < ↑(maxPhiDenOf K_nat thr m) := by
        exact_mod_cast maxPhiDenOf_pos K_nat thr m
      positivity)
    (hφ_lb_le := fun m => by
      have hm1 : (1 : ℝ) ≤ ↑(maxPhiDenOf K_nat thr m) := by exact_mod_cast maxPhiDenOf_pos K_nat thr m
      exact div_le_one_of_le₀ hm1 (by positivity))
    (hφ_lb_anti := fun _ _ hle =>
      one_div_le_one_div_of_le (by exact_mod_cast maxPhiDenOf_pos K_nat thr _)
        (by exact_mod_cast maxPhiDenOf_mono K_nat thr hle))
    (hmaxPhiDen_pos := fun m => maxPhiDenOf_pos K_nat thr m)
    (hC_phi := hCphi_pos)
    (hmaxPhiDen_le := hCphi)
    (hcw_pos := by omega)
    (hC_space := by omega)
    (hspace_le := fun n m => decompSpace_le_poly C_phi c n m)
    (procs := fun b => decomposeProcs K_nat thr P c b)
    (hprocs_nonempty := fun b => decomposeProcs_length_pos K_nat thr P c b)
    (spec := decomposeEntry_spec_aux hK hDec hK_nat hKn1 hthr200 hthr_cr hC₀p hC₁p hphi_sb hCphi_pos hCphi)

@[expose] noncomputable def decomposeImplUsed (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    Spanner.DecomposeImpl :=
  let K := Classical.choose hDec
  let hrest := Classical.choose_spec hDec
  let cr := Classical.choose hrest
  let hrest2 := Classical.choose_spec hrest
  let P := Classical.choose hrest2
  let hrest3 := Classical.choose_spec hrest2
  let c := Classical.choose hrest3
  let hprop := Classical.choose_spec hrest3
  let hK : 0 < K := hprop.1
  let K_nat := max 1 ⌈K⌉₊
  let thr := max 200 (thresholdB1 cr)
  let hsub := maxPhiDenOf_le_subpoly K_nat thr
  let C₀_p := Classical.choose hsub
  let C₁_p' := Classical.choose (Classical.choose_spec hsub)
  let hsub_spec := Classical.choose_spec (Classical.choose_spec hsub)
  let C₁_p := max 1 C₁_p'
  let hlin := maxPhiDenOf_le_linear K_nat thr
  let C_phi := Classical.choose hlin
  let hlin_spec := Classical.choose_spec hlin
  have hK_nat : K ≤ ↑K_nat := le_trans (Nat.le_ceil K) (by exact_mod_cast le_max_right 1 ⌈K⌉₊)
  have hphi_sb : ∀ m, (maxPhiDenOf K_nat thr m : ℝ) ≤ C₁_p * subpolyB1 C₀_p m := fun m => by
    have h1 := hsub_spec.2.2 m
    have hC1_le : C₁_p' ≤ C₁_p := le_max_right _ _
    have hsb := one_le_subpolyB1 hsub_spec.1.le m
    have hmul : C₁_p' * subpolyB1 C₀_p m ≤ C₁_p * subpolyB1 C₀_p m :=
      mul_le_mul_of_nonneg_right hC1_le (by positivity)
    exact le_trans h1 hmul
  mkDecomposeImplAux K cr P c K_nat thr C_phi C₀_p C₁_p hK hprop.2.2 hK_nat
    (le_max_left 1 ⌈K⌉₊) (le_max_left 200 (thresholdB1 cr)) (le_max_right 200 (thresholdB1 cr))
    hsub_spec.1 (le_max_left 1 C₁_p') hphi_sb hlin_spec.1 hlin_spec.2

@[expose] noncomputable def decomposeImpl (hDec : Cited.ExpanderDecomposition) : Spanner.DecomposeImpl :=
  decomposeImplUsed (.of_cited hDec)

lemma decomposeImplUsed_noRand (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    ∀ b s, s ∈ (decomposeImplUsed hDec).procs b → s.NoRand := by
  intro b s hs
  dsimp only [decomposeImplUsed, mkDecomposeImplAux] at hs
  exact decomposeProcs_noRand _ _ _ _ b s hs

lemma decomposeImplUsed_c_ell (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    (decomposeImplUsed hDec).c_ℓ = 1 := rfl

lemma decomposeImplUsed_decFactor_eq (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ (decomposeImplUsed hDec).decFactor = subpolyB1 C₀ := by
  dsimp only [decomposeImplUsed, mkDecomposeImplAux]
  refine ⟨_, ?_, rfl⟩
  positivity

lemma decomposeImpl_noRand (hDec : Cited.ExpanderDecomposition) :
    ∀ b s, s ∈ (decomposeImpl hDec).procs b → s.NoRand :=
  decomposeImplUsed_noRand (.of_cited hDec)

lemma decomposeImpl_c_ell (hDec : Cited.ExpanderDecomposition) :
    (decomposeImpl hDec).c_ℓ = 1 := rfl

lemma decomposeImpl_decFactor_eq (hDec : Cited.ExpanderDecomposition) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ (decomposeImpl hDec).decFactor = subpolyB1 C₀ :=
  decomposeImplUsed_decFactor_eq (.of_cited hDec)

end

end MinCostFlow.Expander
