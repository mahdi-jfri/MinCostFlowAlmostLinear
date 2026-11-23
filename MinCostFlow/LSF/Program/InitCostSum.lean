module

public import MinCostFlow.LSF.Program.InitCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The total cost of the init driver

The tree phase makes the weighted copies of the edges of `G₀` and calls the `[AN19]` program on
them. Its cost depends on the number `M` of copies, which is at most `2 m₀`, and the cost of the
`[AN19]` program grows with the number of edges. So `treeBound` charges the `[AN19]` call at
`2 m₀` edges (`treeCostOf_le`). The rest of the tree phase costs `O((m₀ + n₀ + 1) L_sim ²)`
(`treeNat_le`).

`initCost_total_le` adds the bounds of all segments and the initial potential and compares the sum
with `lsfInitCost`: everything except the `[AN19]` call is at most
`150000 (m₀ + n₀ + 1) (L ^ 4 + L_w ^ 2 + L_sim ^ 2 + 1)`, the call is at most
`32000 (m₀ + n₀ + 1) lsstOverheadFactorH`, and both factors are at most `lsfOverhead`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- The tree phase without the `[AN19]` call: the copies, the limb count and the bookkeeping. -/
def treeNat (V : InitVals) : ℕ :=
  initTreeQNatCost V.m0 V.L_in V.K_w + 100 * V.m0 * V.L_in + 600 * V.m0 + 20 * V.n0 + 400 +
    (40 * Nat.log 2 (16 * (2 * V.m0) + 6) + 100) + 60 * V.n0 + 80 * (2 * V.m0 + V.n0) + 300

/-- The bound on the cost of the tree phase, with the `[AN19]` call charged at `2 m₀` edges. -/
noncomputable def treeBound (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ) (V : InitVals) : ℕ :=
  treeNat V +
    lsstCost Q_AN K_AN c_AN V.n0 (2 * V.m0) V.L_in (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h

/-- The cost of the `[AN19]` program grows with the number of edges. -/
lemma lsstCost_mono_m {Q_AN : Program} {K_AN : ℝ} {c_AN n m₁ m₂ L Ls h : ℕ} (hL : 1 ≤ Ls)
    (hh : 1 ≤ h) (hm : m₁ ≤ m₂) :
    lsstCost Q_AN K_AN c_AN n m₁ L Ls h ≤ lsstCost Q_AN K_AN c_AN n m₂ L Ls h := by
  have hc := anCostBound_mono_m (K_AN := K_AN) (n := n) hL hh hm
  have hw := w'Max_mono_m (c_AN := c_AN) (n := n) (L := L) (h := h) hm
  have hk := kWidthOf_mono (L := L) hm
  have h2 : 2 * m₁ - 1 ≤ 2 * m₂ - 1 := by omega
  simp only [lsstCost, scanNonloopsCost, starPairsCost, buildCSRCost, buildVertIdxCost,
    bfsBridgesCost, weightsCost, weightStepCost, simDecodeCost, decodeOutCost]
  gcongr

/-- The tree phase costs at most `treeBound`, for every edge list of `G₀`. -/
lemma treeCostOf_le {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {w h : ℕ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {V : InitVals} {lenArr wtArr : ℕ} {vList eList : List ℕ}
    (hh : 1 ≤ h) (hv : ∀ e ∈ G₀.E, 0 < v e) (hm : G₀.E.card = V.m0)
    (heLen : eList.length = V.m0) (heNd : eList.Nodup) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E) :
    treeCostOf Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp V lenArr wtArr vList eList ≤
      treeBound Q_AN c_AN K_AN h V := by
  have hM : treePhaseM G₀ v vList eList ≤ 2 * V.m0 := by
    have := edgeMult_sum_le_two_mul hv (heLen.trans hm.symm) heNd heE
      (mult := treeMult G₀ v eList) (fun j _ => rfl)
    simp only [treePhaseM, copyIndexedGraph, copyList_length]
    omega
  have hLs1 : 1 ≤ lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h :=
    le_trans (by unfold kWidthOf; omega) (le_max_left _ _)
  have hmono := lsstCost_mono_m (Q_AN := Q_AN) (K_AN := K_AN) (c_AN := c_AN) (n := V.n0)
    (L := V.L_in) hLs1 hh hM
  simp only [treeCostOf, treePhaseContract, treePhaseCopyArgs_treeArgsV,
    treePhaseLsstArgs_treeArgsV, treeCopiesContract, lsimContract, treeLsstContract, treeBound,
    treeNat]
  simp only [treeArgsV, treeCopyArgsV, List.cons_append, List.getD_cons_succ,
    List.getD_cons_zero]
  omega

/-- The integer division scratch of `multQNatStepProc` is at most `80 s ^ 2`. -/
private lemma multQNatStepSpace_le {K s : ℕ} (hK : K ≤ s) (hs : 4 ≤ s) :
    multQNatStepSpace K ≤ 80 * s ^ 2 := by
  simp only [multQNatStepSpace, Num.integerDivideSpace, Num.unsignedDivideSpace]
  have h1 : K * (K + 1) ≤ s * (s + 1) := Nat.mul_le_mul hK (by omega)
  have h2 : (K + 6) * (K + 6 + 1) ≤ (3 * s) * (4 * s) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 4 * s ≤ s ^ 2 := by nlinarith
  nlinarith

/-- The tree phase without the `[AN19]` call costs at most `20000 (m₀ + n₀ + 1) Ls ^ 2`. -/
lemma treeNat_le (V : InitVals) {Ls : ℕ} (hK : V.K_w ≤ Ls) (hL : V.L_in ≤ Ls)
    (hlog : Nat.log 2 (16 * (2 * V.m0) + 6) ≤ Ls) (hs : 4 ≤ Ls) :
    treeNat V ≤ 20000 * (V.m0 + V.n0 + 1) * Ls ^ 2 := by
  have hmq := multQNatStepSpace_le hK hs
  have hK6 : (V.K_w + 6) ^ 2 ≤ 9 * Ls ^ 2 := by
    have : V.K_w + 6 ≤ 3 * Ls := by omega
    calc (V.K_w + 6) ^ 2 ≤ (3 * Ls) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 9 * Ls ^ 2 := by ring
  have h16 : 4 * Ls ≤ Ls ^ 2 := by nlinarith
  have hb : 800 * (V.K_w + 6) ^ 2 + 2800 * (V.K_w + 6) + 16 * multQNatStepSpace V.K_w +
      25 * V.L_in + 2300 ≤ 12000 * Ls ^ 2 := by omega
  have hb' := Nat.mul_le_mul_left V.m0 hb
  have hmL : V.m0 * V.L_in ≤ V.m0 * Ls ^ 2 := Nat.mul_le_mul_left _ (by omega)
  have hm1 : V.m0 ≤ V.m0 * Ls ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hn1 : V.n0 ≤ V.n0 * Ls ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  simp only [treeNat, initTreeQNatCost]
  nlinarith

lemma lsstLSimMin_n_eq (c_AN n m L h : ℕ) :
    lsstLSimMin c_AN 0 m L h = lsstLSimMin c_AN n m L h := rfl

/-- The square of the limb count is part of `lsstOverheadFactorH`. -/
lemma lsim_sq_le_overheadH (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (n m L h : ℕ) (hh : 1 ≤ h) :
    ((lsstLSimMin c_AN n m L h : ℕ) : ℝ) ^ 2 ≤ lsstOverheadFactorH Q_AN c_AN K_AN n m L h := by
  dsimp only [lsstOverheadFactorH]
  set L_sim := lsstLSimMin c_AN n m L h
  have h1L : 1 ≤ L_sim := le_trans (by unfold kWidthOf; omega) (le_max_left _ _)
  have hpow2 : 2 ≤ 2 ^ (L_sim * h) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_pos h1L hh))
  have hwf := logLog_add_weightFactor_nonneg n _ hpow2
  have hK1 : 0 ≤ max K_AN 1 := le_trans (by norm_num) (le_max_right K_AN 1)
  have : 0 ≤ (simScale Q_AN : ℝ) * (L_sim : ℝ) * (w'Max c_AN n m L h : ℝ) *
      (max K_AN 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) + 1) := by
    refine mul_nonneg (by positivity) ?_
    linarith [mul_nonneg hK1 hwf]
  linarith

/-- The arithmetic of `initCost_total_le` in `ℕ`. -/
private lemma cost_sum_nat {a b c d e f tb tn T L Ls W m n : ℕ}
    (hABF : a + b + f ≤ tb + 3000 * (m + n + 1) * (L + Ls)) (htb : tb = tn + T)
    (hC : c ≤ 20000 * (m + n + 1) * (L ^ 4 + W ^ 2 + Ls ^ 2 + 1))
    (hD : d ≤ 100000 * (m + n + 1) * (L ^ 4 + W ^ 2 + 1))
    (hE : e ≤ 3000 * (n + 1) * L ^ 4)
    (hT : tn ≤ 20000 * (m + n + 1) * Ls ^ 2) :
    a + b + c + d + e + f + 3000 * (n + 1) * L + 2 ≤
      T + 150000 * ((m + n + 1) * (L ^ 4 + W ^ 2 + Ls ^ 2 + 1)) := by
  set X := m + n + 1
  set Qn := L ^ 4 + W ^ 2 + Ls ^ 2 + 1
  have q1 : L + Ls ≤ Qn := by
    have : L ≤ L ^ 4 := Nat.le_self_pow (by norm_num) L
    have : Ls ≤ Ls ^ 2 := Nat.le_self_pow (by norm_num) Ls
    omega
  have q2 : L ^ 4 + W ^ 2 + 1 ≤ Qn := by omega
  have q3 : L ^ 4 ≤ Qn := by omega
  have q4 : Ls ^ 2 ≤ Qn := by omega
  have q5 : L ≤ Qn := by
    have : L ≤ L ^ 4 := Nat.le_self_pow (by norm_num) L
    omega
  have x2 : n + 1 ≤ X := by omega
  have p1 : 3000 * X * (L + Ls) ≤ 3000 * (X * Qn) :=
    (Nat.mul_le_mul_left _ q1).trans_eq (by ring)
  have p2 : 100000 * X * (L ^ 4 + W ^ 2 + 1) ≤ 100000 * (X * Qn) :=
    (Nat.mul_le_mul_left _ q2).trans_eq (by ring)
  have p3 : 3000 * (n + 1) * L ^ 4 ≤ 3000 * (X * Qn) :=
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ x2) q3).trans_eq (by ring)
  have p4 : 20000 * X * Ls ^ 2 ≤ 20000 * (X * Qn) :=
    (Nat.mul_le_mul_left _ q4).trans_eq (by ring)
  have p5 : 3000 * (n + 1) * L ≤ 3000 * (X * Qn) :=
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ x2) q5).trans_eq (by ring)
  have p6 : 20000 * X * Qn = 20000 * (X * Qn) := by ring
  have p7 : 1 ≤ X * Qn := Nat.mul_pos (by omega) (by omega)
  omega

/-- All segments of the init driver, the initial potential, and `+ 20` slack for the top-level
`n₀ = 1` branch, against `lsfInitCost`. -/
theorem initCost_total_le_slack (Q_AN : Program) {c_AN : ℕ} (K_AN : ℝ) {h : ℕ} (V : InitVals)
    (hc : 1 ≤ c_AN) (hh : 1 ≤ h) (hn1 : 1 ≤ V.n0)
    (hKw : V.K_w = kWidthOf V.m0 V.L_in) (hKK : V.K = widthK V.m0 V.L_in) :
    segACost V.n0 + segBCost V.n0 V.m0 (treeBound Q_AN c_AN K_AN h V) + segCCost V +
        segDCost V V.n0 + segECost V + segFCost + 3000 * (V.n0 + 1) * initLg V.n0 + 2 + 20 ≤
      lsfInitCostFactor * Nat.ceil (((V.m0 + V.n0 + 1 : ℕ) : ℝ) *
        lsfOverhead Q_AN c_AN K_AN V.n0 V.m0 V.L_in V.L_w h) := by
  set Ls := lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h with hLsdef
  set T := lsstCost Q_AN K_AN c_AN V.n0 (2 * V.m0) V.L_in Ls h
  -- the facts on `Ls`
  have hKw2 : V.K_w ≤ Ls := by
    rw [hKw]
    exact (kWidthOf_mono (by omega : V.m0 ≤ 2 * V.m0)).trans (le_max_left _ _)
  have hKs : kWidthOf (2 * V.m0) V.L_in ≤ Ls := le_max_left _ _
  have hLin : V.L_in ≤ Ls := le_trans (by unfold kWidthOf; omega) hKs
  have hs4 : 4 ≤ Ls := by
    have : 0 < Nat.log 2 (4 * (2 * V.m0) + 2) := Nat.log_pos (by norm_num) (by omega)
    exact le_trans (by unfold kWidthOf; omega) hKs
  have hlog : Nat.log 2 (16 * (2 * V.m0) + 6) ≤ Ls := by
    have h1 : Nat.log 2 (16 * (2 * V.m0) + 6) ≤ w'Max c_AN 0 (2 * V.m0) V.L_in h := by
      simp only [w'Max]
      rw [show 6 + 16 * (2 * V.m0) = 16 * (2 * V.m0) + 6 by omega]
      calc Nat.log 2 (16 * (2 * V.m0) + 6)
          ≤ 1 * (Nat.log 2 (16 * (2 * V.m0) + 6) + kWidthOf (2 * V.m0) V.L_in * h + 3) := by
            omega
        _ ≤ _ := Nat.mul_le_mul_right _ hc
    exact h1.trans (le_max_right _ _)
  -- the segment bounds
  have hABF := segABFCost_le (n0 := V.n0) (m0 := V.m0) (Bt := treeBound Q_AN c_AN K_AN h V)
    (log_m_le_lsim (c_AN := c_AN) (L_in := V.L_in) (h := h))
  have hC := segCCost_le V (widthK_le_lsim (h := h) (m0 := V.m0) (L_in := V.L_in) hc |>.trans'
    (le_of_eq hKK))
  have hD := segDCost_le V
  have hE := segECost_le V
  have hT := treeNat_le V hKw2 hLin hlog hs4
  have hTB : treeBound Q_AN c_AN K_AN h V = treeNat V + T := rfl
  have hnat := cost_sum_nat hABF hTB hC hD hE hT
  -- the `[AN19]` call
  have hTr : (T : ℝ) ≤ 16000 * ((2 * V.m0 + V.n0 + 1 : ℕ) : ℝ) *
      lsstOverheadFactorH Q_AN c_AN K_AN V.n0 (2 * V.m0) V.L_in h := by
    have := lsstCost_le_linear_factor_h Q_AN c_AN K_AN (n := V.n0) (m := 2 * V.m0)
      (L := V.L_in) hn1 hh
    rwa [← lsstLSimMin_n_eq] at this
  -- the factors against `lsfOverhead`
  set L := initLg V.n0
  set W := V.L_w
  set X := V.m0 + V.n0 + 1
  set Qn := L ^ 4 + W ^ 2 + Ls ^ 2 + 1
  set F := lsfOverhead Q_AN c_AN K_AN V.n0 V.m0 V.L_in V.L_w h
  set FH := lsstOverheadFactorH Q_AN c_AN K_AN V.n0 (2 * V.m0) V.L_in h
  have hFH : FH ≤ F := (lsfOverhead_bounds Q_AN c_AN K_AN V.n0 V.m0 V.L_in V.L_w h hh).1
  have hFH1 : 1 ≤ FH := lsstOverheadFactorH_ge_one Q_AN c_AN K_AN V.n0 (2 * V.m0) V.L_in h hh
  have hLsFH : ((Ls : ℕ) : ℝ) ^ 2 ≤ FH := by
    rw [hLsdef, lsstLSimMin_n_eq c_AN V.n0]
    exact lsim_sq_le_overheadH Q_AN c_AN K_AN V.n0 (2 * V.m0) V.L_in h hh
  have hQF : (Qn : ℝ) ≤ F := by
    simp only [Qn, F, lsfOverhead, L, initLg]
    push_cast
    linarith
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hXF : (X : ℝ) * Qn ≤ X * F := mul_le_mul_of_nonneg_left hQF hX0
  have h2X : ((2 * V.m0 + V.n0 + 1 : ℕ) : ℝ) ≤ 2 * X := by
    exact_mod_cast (by omega : 2 * V.m0 + V.n0 + 1 ≤ 2 * X)
  have hTF : (T : ℝ) ≤ 32000 * (X * F) := by
    have hFH0 : (0 : ℝ) ≤ FH := by linarith
    calc (T : ℝ) ≤ 16000 * ((2 * V.m0 + V.n0 + 1 : ℕ) : ℝ) * FH := hTr
      _ ≤ 16000 * (2 * X) * F := by
          refine mul_le_mul (by linarith) hFH hFH0 (by positivity)
      _ = 32000 * (X * F) := by ring
  have hceil : (X : ℝ) * F ≤ Nat.ceil ((X : ℝ) * F) := Nat.le_ceil _
  generalize segACost V.n0 + segBCost V.n0 V.m0 (treeBound Q_AN c_AN K_AN h V) + segCCost V +
      segDCost V V.n0 + segECost V + segFCost + 3000 * (V.n0 + 1) * L + 2 = S at hnat ⊢
  generalize Nat.ceil ((X : ℝ) * F) = cF at hceil ⊢
  generalize hP : X * Qn = P at hnat
  have hPr : (P : ℝ) = (X : ℝ) * Qn := by rw [← hP]; push_cast; ring
  have hcast : (S : ℝ) ≤ (T : ℝ) + 150000 * (P : ℝ) := by exact_mod_cast hnat
  have hfac : ((lsfInitCostFactor * cF : ℕ) : ℝ) = 200000 * (cF : ℝ) := by
    simp only [lsfInitCostFactor]; push_cast; ring
  have hXF1 : (1 : ℝ) ≤ (X : ℝ) * F := one_le_mul_of_one_le_of_one_le hX1 (le_trans hFH1 hFH)
  have hfin : ((S + 20 : ℕ) : ℝ) ≤ ((lsfInitCostFactor * cF : ℕ) : ℝ) := by
    rw [hfac]; push_cast; linarith
  exact_mod_cast hfin

/-- All segments of the init driver and the initial potential, against `lsfInitCost`. The
tree phase is charged by `treeBound`, the potential by the bound of `lsfPhi_init_le`, and the
`2` steps that the call sequence needs at its end (`SeqWP`). -/
theorem initCost_total_le (Q_AN : Program) {c_AN : ℕ} (K_AN : ℝ) {h : ℕ} (V : InitVals)
    (hc : 1 ≤ c_AN) (hh : 1 ≤ h) (hn1 : 1 ≤ V.n0)
    (hKw : V.K_w = kWidthOf V.m0 V.L_in) (hKK : V.K = widthK V.m0 V.L_in) :
    segACost V.n0 + segBCost V.n0 V.m0 (treeBound Q_AN c_AN K_AN h V) + segCCost V +
        segDCost V V.n0 + segECost V + segFCost + 3000 * (V.n0 + 1) * initLg V.n0 + 2 ≤
      lsfInitCostFactor * Nat.ceil (((V.m0 + V.n0 + 1 : ℕ) : ℝ) *
        lsfOverhead Q_AN c_AN K_AN V.n0 V.m0 V.L_in V.L_w h) :=
  le_trans (Nat.le_add_right _ 20) (initCost_total_le_slack Q_AN K_AN V hc hh hn1 hKw hKK)

end

end MinCostFlow.LSF.Program
