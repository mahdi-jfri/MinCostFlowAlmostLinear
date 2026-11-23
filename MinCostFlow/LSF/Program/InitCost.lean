module

public import MinCostFlow.LSF.Program.InitMain

/-!
# The cost of the init driver, segment by segment

The cost bound `lsfInitCost` charges `(m₀ + n₀ + 1)` times `lsfOverhead`, which holds the term
`L ^ 4 + L_w ^ 2 + 1` with `L = log₂ (n₀ + 2) + 1` (`initLg`). Here we bound the costs of the
segments of `main_wp` that do not call the tree module by multiples of `(m₀ + n₀ + 1)` times
that term. The logarithms that the segments use (`log₂ n₀`, `⌈log₂ n₀⌉`, `auxLogCap n₀`) are at
most `L`, and the depth bound `hldDepthBound n₀ + 1` is at most `2 L ^ 2`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver WideWord

@[expose] public section

/-- The logarithm `log₂ (n + 2) + 1` of `lsfOverhead`. -/
def initLg (n : ℕ) : ℕ := Nat.log 2 (n + 2) + 1

lemma initLg_pos (n : ℕ) : 1 ≤ initLg n := by simp only [initLg]; omega

lemma initLg_two (n : ℕ) : 2 ≤ initLg n := by
  have : 0 < Nat.log 2 (n + 2) := Nat.log_pos (by norm_num) (by omega)
  simp only [initLg]; omega

lemma log_le_initLg (n : ℕ) : Nat.log 2 n + 1 ≤ initLg n := by
  simp only [initLg]
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1

lemma auxLogCap_le_initLg (n : ℕ) : auxLogCap n ≤ initLg n := by
  simp only [initLg, auxLogCap]
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1

lemma clog_le_initLg (n : ℕ) : Nat.clog 2 n ≤ initLg n := by
  refine (Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num) n).le).trans ?_
  exact log_le_initLg n

lemma hldDepthBound_succ_le (n : ℕ) : hldDepthBound n + 1 ≤ 2 * initLg n ^ 2 := by
  have h := log_le_initLg n
  have h1 := initLg_two n
  simp only [hldDepthBound]
  have : (Nat.log 2 n + 1) * (Nat.log 2 n + 2) ≤ initLg n * (initLg n + 1) :=
    Nat.mul_le_mul h (by omega)
  nlinarith

/-- The forest phase costs at most `3000 (n₀ + 1) L ^ 4`. -/
lemma segECost_le (V : InitVals) :
    segECost V ≤ 3000 * (V.n0 + 1) * initLg V.n0 ^ 4 := by
  have hlc := auxLogCap_le_initLg V.n0
  have hcl := clog_le_initLg V.n0
  have hL := initLg_pos V.n0
  have htM : V.tM ≤ V.n0 := Nat.sub_le _ _
  simp only [segECost, fPhaseCost, FLayout.args, FLayout.ofVals, FLayout.ofDecomp,
    DecompLayout.ofVals, DecompLayout.ofOrder, OrderLayout.ofVals, List.getD_cons_succ,
    List.getD_cons_zero]
  set L := initLg V.n0
  set n := V.n0
  have hL2 : L ≤ L ^ 4 := Nat.le_self_pow (by norm_num) L
  have hL3 : L * L ≤ L ^ 4 := by nlinarith
  have e1 : n * auxLogCap n ≤ n * L := Nat.mul_le_mul_left n hlc
  have e2 : (270 * auxLogCap n + 180) * n * (Nat.clog 2 n + 1) ≤ (450 * L) * n * (2 * L) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right n (by omega)) (by omega)
  have e3 : n * L ≤ n * L ^ 4 := Nat.mul_le_mul_left n hL2
  have e4 : n * (L * L) ≤ n * L ^ 4 := Nat.mul_le_mul_left n hL3
  have e5 : 1 ≤ L ^ 4 := Nat.one_le_pow _ _ hL
  nlinarith

/-- The monomials that the segment costs use are at most `L ^ 4 + W ^ 2 + 1`. -/
lemma initOv_facts {L W : ℕ} (hL : 2 ≤ L) :
    L ≤ L ^ 4 + W ^ 2 + 1 ∧ L ^ 2 ≤ L ^ 4 + W ^ 2 + 1 ∧ L ^ 3 ≤ L ^ 4 + W ^ 2 + 1 ∧
    L ^ 2 * W ≤ L ^ 4 + W ^ 2 + 1 ∧ W ≤ L ^ 4 + W ^ 2 + 1 := by
  have h1 : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) L
  have h2 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : L ^ 3 ≤ L ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 2 * (L ^ 2 * W) ≤ L ^ 4 + W ^ 2 := by
    zify; nlinarith [sq_nonneg ((L : ℤ) ^ 2 - W)]
  have h5 : W ≤ W ^ 2 + 1 := by nlinarith
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The decomposition phase (with the stretches) costs at most
`100000 (m₀ + n₀ + 1) (L ^ 4 + L_w ^ 2 + 1)`. -/
lemma segDCost_le (V : InitVals) :
    segDCost V V.n0 ≤
      100000 * (V.m0 + V.n0 + 1) * (initLg V.n0 ^ 4 + V.L_w ^ 2 + 1) := by
  have hlc := auxLogCap_le_initLg V.n0
  have hL := initLg_two V.n0
  have hD := hldDepthBound_succ_le V.n0
  have htM : V.tM ≤ V.n0 := Nat.sub_le _ _
  simp only [segDCost, decompPhaseCost, wstrCopyEdgesCost, DecompLayout.args, DecompLayout.ofVals,
    DecompLayout.ofOrder, OrderLayout.ofVals, List.getD_cons_succ, List.getD_cons_zero]
  have hl2 : Nat.log 2 (V.n0 + 1) ≤ initLg V.n0 := by
    have := Nat.log_mono_right (b := 2) (show V.n0 + 1 ≤ V.n0 + 2 by omega)
    simp only [initLg]; omega
  have hl4 : Nat.log 2 (V.n0 + 2) ≤ initLg V.n0 := by simp only [initLg]; omega
  set L := initLg V.n0
  set n := V.n0
  set m := V.m0
  set W := V.L_w
  set D := hldDepthBound n
  have hl3 : Nat.log 2 (D + 2) ≤ 2 * L ^ 2 + 1 :=
    (Nat.log_lt_self 2 (by omega : D + 2 ≠ 0)).le.trans (by omega)
  have hLL : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) L
  have hL4 : 4 ≤ L ^ 2 := by nlinarith
  have hLB : wstrLB n D W ≤ W + 6 * L ^ 2 := by
    simp only [wstrLB]
    omega
  -- monotonicity: replace `tM`, `LB`, `logCap` and `D + 1` by their bounds
  have hW : wstrCost n V.tM m (wstrLB n D W) (auxLogCap n) ≤
      2 * L ^ 2 * (400 * n + 30 * n + n * (100 * L + 400 * (W + 6 * L ^ 2) + 400) +
        m * (150 * (W + 6 * L ^ 2) + 160) + 600) +
      m * (200 * (W + 6 * L ^ 2) * (W + 6 * L ^ 2) + 1100 * (W + 6 * L ^ 2) + 100 * L + 1200) +
      n * (200 * (W + 6 * L ^ 2) + 300) + n * (30 * (W + 6 * L ^ 2) + 80) +
      500 * (W + 6 * L ^ 2) * (W + 6 * L ^ 2) + 1000 * (W + 6 * L ^ 2) + 40 * L + 2000 := by
    simp only [wstrCost]
    gcongr
  obtain ⟨q1, q2, q3, q4, q5⟩ := initOv_facts (W := W) hL
  set Q := L ^ 4 + W ^ 2 + 1
  have q6 : W ^ 2 ≤ Q := by omega
  have q7 : L ^ 4 ≤ Q := by omega
  have k1 := Nat.mul_le_mul_left n q1; have k2 := Nat.mul_le_mul_left n q2
  have k3 := Nat.mul_le_mul_left n q3; have k4 := Nat.mul_le_mul_left n q4
  have k5 := Nat.mul_le_mul_left n q5; have k6 := Nat.mul_le_mul_left n q6
  have k7 := Nat.mul_le_mul_left n q7
  have j1 := Nat.mul_le_mul_left m q1; have j2 := Nat.mul_le_mul_left m q2
  have j3 := Nat.mul_le_mul_left m q3; have j4 := Nat.mul_le_mul_left m q4
  have j5 := Nat.mul_le_mul_left m q5; have j6 := Nat.mul_le_mul_left m q6
  have j7 := Nat.mul_le_mul_left m q7
  have hnQ : n ≤ n * Q := Nat.le_mul_of_pos_right n (by omega)
  have hmQ : m ≤ m * Q := Nat.le_mul_of_pos_right m (by omega)
  have hDn : D * (70 * n + 80) ≤ 2 * L ^ 2 * (70 * n + 80) :=
    Nat.mul_le_mul_right _ (by omega)
  have htm : 30 * V.tM ≤ 30 * n := by omega
  nlinarith

lemma log_two_mul_le_initLg (n : ℕ) : Nat.log 2 (2 * n) ≤ initLg n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2)
  rw [Nat.succ_eq_add_one, pow_succ] at h1
  have h2 : 2 * n < 2 ^ (initLg n + 1) := by
    simp only [initLg]; rw [pow_succ, pow_succ]; omega
  have := Nat.log_lt_of_lt_pow (by omega) h2
  omega

/-- The width `widthK m₀ L_in` of the order phase is at most `2 L_sim + 7`. -/
lemma widthK_le_lsim {c_AN m0 L_in h : ℕ} (hc : 1 ≤ c_AN) :
    widthK m0 L_in ≤ 2 * lsstLSimMin c_AN 0 (2 * m0) L_in h + 7 := by
  have h1 : kWidthOf m0 L_in ≤ kWidthOf (2 * m0) L_in := by
    simp only [kWidthOf]
    have := Nat.log_mono_right (b := 2) (show 4 * m0 + 2 ≤ 4 * (2 * m0) + 2 by omega)
    omega
  have h2 : kWidthOf (2 * m0) L_in ≤ lsstLSimMin c_AN 0 (2 * m0) L_in h := le_max_left _ _
  have h3 : Nat.log 2 (m0 + 1) ≤ w'Max c_AN 0 (2 * m0) L_in h := by
    simp only [w'Max]
    have := Nat.log_mono_right (b := 2) (show m0 + 1 ≤ 6 + 16 * (2 * m0) by omega)
    calc Nat.log 2 (m0 + 1) ≤ 1 * (Nat.log 2 (6 + 16 * (2 * m0)) + kWidthOf (2 * m0) L_in * h + 3) :=
          by omega
      _ ≤ _ := Nat.mul_le_mul_right _ hc
  have h4 : w'Max c_AN 0 (2 * m0) L_in h ≤ lsstLSimMin c_AN 0 (2 * m0) L_in h := le_max_right _ _
  simp only [widthK]
  omega

/-- The order phase costs at most `20000 (m₀ + n₀ + 1) (L ^ 4 + L_w ^ 2 + Ls ^ 2 + 1)`
when its width `K` is at most `2 Ls + 7`. -/
lemma segCCost_le (V : InitVals) {Ls : ℕ} (hK : V.K ≤ 2 * Ls + 7) :
    segCCost V ≤
      20000 * (V.m0 + V.n0 + 1) * (initLg V.n0 ^ 4 + V.L_w ^ 2 + Ls ^ 2 + 1) := by
  have hlc := auxLogCap_le_initLg V.n0
  have hcl := clog_le_initLg V.n0
  have hbst := log_two_mul_le_initLg V.n0
  have hL := initLg_two V.n0
  have htM : V.tM ≤ V.n0 := Nat.sub_le _ _
  simp only [segCCost, orderPhaseCost, OrderLayout.args, OrderLayout.ofVals, bstLoopCost,
    List.getD_cons_succ, List.getD_cons_zero]
  set L := initLg V.n0
  set n := V.n0
  set m := V.m0
  set W := V.L_w
  set K := V.K
  set lc := auxLogCap n
  set Q := L ^ 4 + W ^ 2 + Ls ^ 2 + 1
  have hLL : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) L
  have hL24 : L ^ 2 ≤ L ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hLsL : 2 * (Ls * L) ≤ Ls ^ 2 + L ^ 2 := by
    zify; nlinarith [sq_nonneg ((Ls : ℤ) - L)]
  have hLs : Ls ≤ Ls ^ 2 + 1 := by nlinarith
  have q1 : L ≤ Q := by omega
  have q2 : Ls ≤ Q := by omega
  have q3 : Ls * L ≤ Q := by omega
  have q4 : L ^ 2 ≤ Q := by omega
  have k1 := Nat.mul_le_mul_left n q1; have k2 := Nat.mul_le_mul_left n q2
  have k3 := Nat.mul_le_mul_left n q3; have k4 := Nat.mul_le_mul_left n q4
  have j1 := Nat.mul_le_mul_left m q1; have j2 := Nat.mul_le_mul_left m q2
  have hnQ : n ≤ n * Q := Nat.le_mul_of_pos_right n (by omega)
  have hmQ : m ≤ m * Q := Nat.le_mul_of_pos_right m (by omega)
  have a1 : n * lc ≤ n * L := Nat.mul_le_mul_left n hlc
  have a2 : m * (100 * lc + 300 * K + 420) ≤ m * (100 * L + 300 * (2 * Ls + 7) + 420) :=
    Nat.mul_le_mul_left m (by omega)
  have a3 : (90 * K + 180) * n * (Nat.clog 2 n + 1) ≤
      (90 * (2 * Ls + 7) + 180) * n * (2 * L) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right n (by omega)) (by omega)
  have a4 : n * K ≤ n * (2 * Ls + 7) := Nat.mul_le_mul_left n hK
  have a5 : n * (120 * Nat.log 2 (2 * n) + 4 + 500) ≤ n * (120 * L + 504) :=
    Nat.mul_le_mul_left n (by omega)
  nlinarith

/-- The logarithm of the number of edges that the second segment uses is at most `L_sim`. -/
lemma log_m_le_lsim {c_AN m0 L_in h : ℕ} :
    Nat.log 2 (4 * m0 + 2) ≤ lsstLSimMin c_AN 0 (2 * m0) L_in h := by
  have h1 : Nat.log 2 (4 * m0 + 2) ≤ kWidthOf (2 * m0) L_in := by
    simp only [kWidthOf]
    have := Nat.log_mono_right (b := 2) (show 4 * m0 + 2 ≤ 4 * (2 * m0) + 2 by omega)
    omega
  exact h1.trans (le_max_left _ _)

/-- The first, second and last segments cost at most `Bt + 3000 (m₀ + n₀ + 1) (L + Ls)`,
where `Bt` bounds the tree phase. -/
lemma segABFCost_le {n0 m0 Bt Ls : ℕ} (hLs : Nat.log 2 (4 * m0 + 2) ≤ Ls) :
    segACost n0 + segBCost n0 m0 Bt + segFCost ≤ Bt + 3000 * (m0 + n0 + 1) * (initLg n0 + Ls) := by
  have h1 : Nat.log 2 (n0 + 1) ≤ initLg n0 := by
    have := Nat.log_mono_right (b := 2) (show n0 + 1 ≤ n0 + 2 by omega)
    simp only [initLg]; omega
  have h2 : Nat.log 2 n0 ≤ initLg n0 := by
    have := Nat.log_mono_right (b := 2) (show n0 ≤ n0 + 2 by omega)
    simp only [initLg]; omega
  have h3 : Nat.log 2 (m0 + 1) ≤ Ls :=
    (Nat.log_mono_right (show m0 + 1 ≤ 4 * m0 + 2 by omega)).trans hLs
  have hL := initLg_two n0
  have a1 : n0 ≤ n0 * initLg n0 := Nat.le_mul_of_pos_right n0 (by omega)
  have a2 : m0 ≤ m0 * initLg n0 := Nat.le_mul_of_pos_right m0 (by omega)
  simp only [segACost, segBCost, segFCost]
  nlinarith

end

end MinCostFlow.LSF.Program
