module

public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Expander.Components
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic expander decomposition (Theorem B.1)

Proves Theorem B.1 (page 49) from `Cited.ExpanderDecomposition` ([CGLNPS21], Corollary 6.1).

Choosing `r(m) = ⌊(log₂ m)^{1/3}⌋` (`cubeRoot (Nat.log 2 m)`), for `m ≥ M_B1` we have
`1 ≤ r(m) ≤ cr · log m`, yielding conductance `φ = Ω(1 / exp(O((log m)^{2/3} log log m)))`
and runtime `O(n + (m + 2) · exp(O((log m)^{2/3} log log m)))` (note the paper's stated
`φ = Ω̃(1 / exp((log m)^{1/3}))` does not follow from Corollary 6.1, which has `log(m+2)^{K r²}`).
For small graphs `m < M_B1`, decomposing into connected components (`compLabels`) gives zero
inter-part cut edges and conductance `≥ 1 / (M_B1 + 1)`.
-/

public section

namespace MinCostFlow.Expander

open MinCostFlow.Cited Filter Topology

/-! ### Integer cube root and parameter `r` -/

private def cubeRootAux (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if (k + 1) ^ 3 ≤ x then k + 1 else cubeRootAux x k

/-- Integer cube root `⌊x^{1/3}⌋` via bounded downward search. -/
def cubeRoot (x : ℕ) : ℕ :=
  cubeRootAux x x

private lemma cubeRootAux_pow_le (x k : ℕ) : (cubeRootAux x k) ^ 3 ≤ x := by
  induction k with
  | zero => simp [cubeRootAux]
  | succ k ih =>
    unfold cubeRootAux
    split_ifs with h
    · exact h
    · exact ih

private lemma lt_cubeRootAux_succ_pow (x k : ℕ) (hk : x < (k + 1) ^ 3) :
    x < (cubeRootAux x k + 1) ^ 3 := by
  induction k with
  | zero => simpa [cubeRootAux] using hk
  | succ k ih =>
    unfold cubeRootAux
    split_ifs with h
    · exact hk
    · exact ih (by omega)

lemma cubeRoot_pow_le (x : ℕ) : (cubeRoot x) ^ 3 ≤ x :=
  cubeRootAux_pow_le x x

lemma lt_cubeRoot_succ_pow (x : ℕ) : x < (cubeRoot x + 1) ^ 3 := by
  unfold cubeRoot
  apply lt_cubeRootAux_succ_pow
  have h1 : x < x + 1 := Nat.lt_succ_self x
  have h2 : x + 1 ≤ (x + 1) ^ 3 := by
    calc x + 1 = (x + 1) * 1 := (mul_one _).symm
      _ ≤ (x + 1) * ((x + 1) * (x + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = (x + 1) ^ 3 := by ring
  omega

/-- The parameter `r(m) = ⌊(log₂ m)^{1/3}⌋` used when calling `Cited.ExpanderDecomposition`. -/
def rOf (m : ℕ) : ℕ :=
  cubeRoot (Nat.log 2 m)

lemma rOf_zero : rOf 0 = 0 := by
  simp [rOf, cubeRoot, cubeRootAux]

lemma rOf_one : rOf 1 = 0 := by
  simp [rOf, cubeRoot, cubeRootAux]

lemma one_le_rOf {m : ℕ} (hm : 2 ≤ m) : 1 ≤ rOf m := by
  have hlog : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by norm_num) (by omega)
  by_contra hlt
  have h0 : rOf m = 0 := by omega
  have hlt3 := lt_cubeRoot_succ_pow (Nat.log 2 m)
  change Nat.log 2 m < (rOf m + 1) ^ 3 at hlt3
  rw [h0] at hlt3
  omega

lemma rOf_pow_le (m : ℕ) : (rOf m) ^ 3 ≤ Nat.log 2 m :=
  cubeRoot_pow_le (Nat.log 2 m)

lemma lt_rOf_succ_pow (m : ℕ) : Nat.log 2 m < (rOf m + 1) ^ 3 :=
  lt_cubeRoot_succ_pow (Nat.log 2 m)

/-! ### Exponential / logarithmic helper bounds -/

private lemma exp_one_lt_four : Real.exp 1 < 4 := by
  have h1 : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
    linarith
  have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [lt_inv_comm₀ (by norm_num) hpos] at h1
    linarith
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have hsq : Real.exp 1 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [hsq]
  nlinarith

private lemma natLog2_real_le {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have hpow : (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log ((2 : ℝ) ^ (Nat.log 2 m)) ≤ Real.log m := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (le_div_iff₀ hlog2).mpr hlog

private lemma real_log_le_natLog2 {m : ℕ} (hm : 1 ≤ m) :
    Real.log m ≤ ((Nat.log 2 m : ℝ) + 1) * Real.log 2 := by
  have hlt : (m : ℝ) < (2 : ℝ) ^ (Nat.log 2 m + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log m < Real.log ((2 : ℝ) ^ (Nat.log 2 m + 1)) :=
    Real.log_lt_log hmpos hlt
  rw [Real.log_pow] at hlog
  push_cast at hlog
  exact le_of_lt hlog

/-- Threshold above which `1 ≤ rOf m ≤ cr * Real.log m`. -/
noncomputable def thresholdB1 (cr : ℝ) : ℕ :=
  Nat.ceil (Real.exp (Real.sqrt (1 / (cr ^ 3 * Real.log 2)) + 2)) + 4

lemma four_le_thresholdB1 (cr : ℝ) : 4 ≤ thresholdB1 cr := by
  unfold thresholdB1
  omega

lemma rOf_le_cr_log {cr : ℝ} (hcr : 0 < cr) {m : ℕ} (hm : thresholdB1 cr ≤ m) :
    1 ≤ rOf m ∧ (rOf m : ℝ) ≤ cr * Real.log m := by
  have hm4 : 4 ≤ m := le_trans (four_le_thresholdB1 cr) hm
  refine ⟨one_le_rOf (by omega), ?_⟩
  have hm_real : Real.exp (Real.sqrt (1 / (cr ^ 3 * Real.log 2)) + 2) ≤ (m : ℝ) := by
    have h1 : Real.exp (Real.sqrt (1 / (cr ^ 3 * Real.log 2)) + 2) ≤
        (Nat.ceil (Real.exp (Real.sqrt (1 / (cr ^ 3 * Real.log 2)) + 2)) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (Real.sqrt (1 / (cr ^ 3 * Real.log 2)) + 2)) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (by unfold thresholdB1 at hm; omega :
        Nat.ceil (Real.exp (Real.sqrt (1 / (cr ^ 3 * Real.log 2)) + 2)) ≤ m)
    exact le_trans h1 h2
  have hlog_ge : Real.sqrt (1 / (cr ^ 3 * Real.log 2)) + 2 ≤ Real.log m := by
    have h := Real.log_le_log (Real.exp_pos _) hm_real
    simpa [Real.log_exp] using h
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 / (cr ^ 3 * Real.log 2)) := Real.sqrt_nonneg _
  have hlog_pos : 0 < Real.log m := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : 1 / (cr ^ 3 * Real.log 2) < (Real.log m) ^ 2 := by
    have h1 : Real.sqrt (1 / (cr ^ 3 * Real.log 2)) < Real.log m := by linarith
    have hle : 0 ≤ 1 / (cr ^ 3 * Real.log 2) := by positivity
    calc 1 / (cr ^ 3 * Real.log 2)
        = (Real.sqrt (1 / (cr ^ 3 * Real.log 2))) ^ 2 := (Real.sq_sqrt hle).symm
      _ < (Real.log m) ^ 2 := by nlinarith [Real.sqrt_nonneg (1 / (cr ^ 3 * Real.log 2))]
  have hmul : 1 < cr ^ 3 * Real.log 2 * (Real.log m) ^ 2 := by
    have hdenom : 0 < cr ^ 3 * Real.log 2 := by positivity
    have := mul_lt_mul_of_pos_left hsq hdenom
    field_simp at this
    linarith
  have hcube : (rOf m : ℝ) ^ 3 ≤ (cr * Real.log m) ^ 3 := by
    have hr3 : (rOf m : ℝ) ^ 3 ≤ (Nat.log 2 m : ℝ) := by
      exact_mod_cast cubeRoot_pow_le (Nat.log 2 m)
    have hnat : (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := natLog2_real_le (by omega)
    have hdiv : Real.log m / Real.log 2 ≤ (cr * Real.log m) ^ 3 := by
      rw [div_le_iff₀ hlog2]
      calc Real.log m = Real.log m * 1 := (mul_one _).symm
        _ ≤ Real.log m * (cr ^ 3 * Real.log 2 * (Real.log m) ^ 2) :=
          mul_le_mul_of_nonneg_left hmul.le hlog_pos.le
        _ = (cr * Real.log m) ^ 3 * Real.log 2 := by ring
    exact le_trans hr3 (le_trans hnat hdiv)
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num : 3 ≠ 0)).mp hcube

/-! ### Conductance and asymptotic bounds for Theorem B.1 -/

/-- Conductance guaranteed by Theorem B.1 for `ε = a / b` on an `m`-edge graph. -/
noncomputable def phiB1 (K cr : ℝ) (a b m : ℕ) : ℝ :=
  min (1 / ((thresholdB1 cr : ℝ) + 1))
    (((a : ℝ) / b) / (K * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2)))

lemma phiB1_pos {K cr : ℝ} (hK : 0 < K) (_hcr : 0 < cr) {a b : ℕ}
    (ha : 1 ≤ a) (_hb : a ≤ b) (m : ℕ) :
    0 < phiB1 K cr a b m := by
  unfold phiB1
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hlog : 0 < Real.log ((m : ℝ) + 2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hrpow : 0 < Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) := Real.rpow_pos_of_pos hlog _
  exact lt_min (by positivity) (by positivity)

lemma phiB1_le_one (K cr : ℝ) (a b m : ℕ) : phiB1 K cr a b m ≤ 1 := by
  unfold phiB1
  apply min_le_of_left_le
  have hpos : (0 : ℝ) ≤ (thresholdB1 cr : ℝ) := Nat.cast_nonneg _
  rw [div_le_one (by linarith)]
  linarith

lemma phiB1_le_cor (K cr : ℝ) (a b m : ℕ) :
    phiB1 K cr a b m ≤ ((a : ℝ) / b) / (K * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2)) :=
  min_le_right _ _

/-- Asymptotic subpolynomial bound on `1 / phiB1 K cr a b m` and on Corollary 6.1's multiplier:
there is a uniform constant `C₀ > 0` (independent of `a, b, m`) such that
`1 / phiB1 K cr a b m ≤ max (thresholdB1 cr + 1) (K * b / a) * exp(C₀ * log(m+2)^{2/3} * log(log(m+2)+2))`
and for `m ≥ thresholdB1 cr`,
`(m + 2)^{K / rOf m} * log(m+2)^{K * rOf m ^ 2} ≤ exp(C₀ * log(m+2)^{2/3} * log(log(m+2)+2))`. -/
lemma subpoly_exp_bounds {K cr : ℝ} (hK : 0 < K) (_hcr : 0 < cr) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      (∀ (a b m : ℕ), 1 ≤ a → a ≤ b →
        1 / phiB1 K cr a b m ≤
          max ((thresholdB1 cr : ℝ) + 1) (K * (b : ℝ) / a) *
            Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((m : ℝ) + 2) + 2))) ∧
      (∀ m : ℕ, thresholdB1 cr ≤ m →
        ((m : ℝ) + 2) ^ (K / (rOf m : ℝ)) * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) ≤
          Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((m : ℝ) + 2) + 2))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog4 : 1 < Real.log 4 := by
    have h4 : Real.exp 1 < 4 := exp_one_lt_four
    have := Real.log_lt_log (Real.exp_pos 1) h4
    simpa [Real.log_exp] using this
  let c1 : ℝ := K * (1 / Real.log 2) ^ (2 / 3 : ℝ)
  let c2 : ℝ := K * (10 * Real.log 2) ^ (1 / 3 : ℝ) / Real.log 3
  let C₀ : ℝ := max (c1 + c2) 1
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr_bound : ∀ m : ℕ, 2 ≤ m →
      Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) ≤
        Real.exp (c1 * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2)) := by
    intro m hm
    set L : ℝ := Real.log ((m : ℝ) + 2)
    have hm4 : (4 : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast (by omega : 4 ≤ m + 2)
    have hL_gt1 : 1 < L := lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) hm4)
    have hL_pos : 0 < L := by linarith
    have hr3 : (rOf m : ℝ) ^ 3 ≤ L / Real.log 2 := by
      have h1 : (rOf m : ℝ) ^ 3 ≤ (Nat.log 2 m : ℝ) := by exact_mod_cast cubeRoot_pow_le (Nat.log 2 m)
      have h2 : (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := natLog2_real_le (by omega)
      have h3 : Real.log m ≤ L := Real.log_le_log (by positivity) (by linarith)
      exact le_trans h1 (le_trans h2 (div_le_div_of_nonneg_right h3 hlog2.le))
    have hr_le : (rOf m : ℝ) ≤ (L / Real.log 2) ^ (1 / 3 : ℝ) := by
      have hrp : 0 ≤ (L / Real.log 2) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
      rw [← pow_le_pow_iff_left₀ (Nat.cast_nonneg _) hrp (by norm_num : 3 ≠ 0)]
      have : ((L / Real.log 2) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = L / Real.log 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [this]
      exact hr3
    have hr2_le : (rOf m : ℝ) ^ 2 ≤ (1 / Real.log 2) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
      have hr_nonneg : 0 ≤ (rOf m : ℝ) := Nat.cast_nonneg _
      have hsq : (rOf m : ℝ) ^ 2 ≤ ((L / Real.log 2) ^ (1 / 3 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hr_nonneg hr_le 2
      have hmul : ((L / Real.log 2) ^ (1 / 3 : ℝ)) ^ (2 : ℕ) =
          (1 / Real.log 2) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have heq : L / Real.log 2 = (1 / Real.log 2) * L := by ring
        rw [heq, Real.mul_rpow (by positivity) hL_pos.le]
        norm_num
      exact le_trans hsq (le_of_eq hmul)
    have hlogL : Real.log L ≤ Real.log (L + 2) :=
      Real.log_le_log hL_pos (by linarith)
    rw [Real.rpow_def_of_pos hL_pos]
    apply Real.exp_le_exp.mpr
    have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg hL_gt1.le
    calc Real.log L * (K * (rOf m : ℝ) ^ 2)
        = K * (rOf m : ℝ) ^ 2 * Real.log L := by ring
      _ ≤ K * ((1 / Real.log 2) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ)) * Real.log (L + 2) := by
          apply mul_le_mul _ hlogL hlogL_nonneg (by positivity)
          exact mul_le_mul_of_nonneg_left hr2_le hK.le
      _ = c1 * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by dsimp [c1]; ring
  refine ⟨C₀, hC₀_pos, ?_, ?_⟩
  · intro a b m ha hb
    unfold phiB1
    have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hL_pos : 0 < Real.log ((m : ℝ) + 2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hrpow_pos : 0 < Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) :=
      Real.rpow_pos_of_pos hL_pos _
    have hleft_pos : 0 < (1 : ℝ) / ((thresholdB1 cr : ℝ) + 1) := by positivity
    have hright_pos : 0 < ((a : ℝ) / b) / (K * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2)) := by
      positivity
    have hinv : 1 / min (1 / ((thresholdB1 cr : ℝ) + 1))
        (((a : ℝ) / b) / (K * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2))) =
        max ((thresholdB1 cr : ℝ) + 1)
          ((K * (b : ℝ) / a) * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2)) := by
      rcases le_total (1 / ((thresholdB1 cr : ℝ) + 1))
          (((a : ℝ) / b) / (K * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2))) with h | h
      · rw [min_eq_left h]
        have h1 : 1 / (1 / ((thresholdB1 cr : ℝ) + 1)) = (thresholdB1 cr : ℝ) + 1 := by field_simp
        rw [h1]
        have h2 : (K * (b : ℝ) / a) * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) ≤
            (thresholdB1 cr : ℝ) + 1 := by
          have := one_div_le_one_div_of_le hleft_pos h
          field_simp at this ⊢
          nlinarith
        exact (max_eq_left h2).symm
      · rw [min_eq_right h]
        have h1 : 1 / (((a : ℝ) / b) / (K * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2))) =
            (K * (b : ℝ) / a) * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) := by
          field_simp
        rw [h1]
        have h2 : (thresholdB1 cr : ℝ) + 1 ≤
            (K * (b : ℝ) / a) * Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) := by
          have := one_div_le_one_div_of_le hright_pos h
          field_simp at this ⊢
          nlinarith
        exact (max_eq_right h2).symm
    rw [hinv]
    have hexp_ge1 : 1 ≤ Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((m : ℝ) + 2) + 2)) := by
      apply Real.one_le_exp
      have : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
      positivity
    let Mcoeff := max ((thresholdB1 cr : ℝ) + 1) (K * (b : ℝ) / a)
    have hM_pos : 0 ≤ Mcoeff := le_trans (by positivity) (le_max_left _ _)
    apply max_le
    · calc (thresholdB1 cr : ℝ) + 1 ≤ Mcoeff := le_max_left _ _
        _ = Mcoeff * 1 := (mul_one _).symm
        _ ≤ Mcoeff * Real.exp _ := mul_le_mul_of_nonneg_left hexp_ge1 hM_pos
    · have hpow_bound : Real.log ((m : ℝ) + 2) ^ (K * (rOf m : ℝ) ^ 2) ≤
          Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((m : ℝ) + 2) + 2)) := by
        by_cases hm2 : 2 ≤ m
        · refine le_trans (hr_bound m hm2) (Real.exp_le_exp.mpr ?_)
          have hc1_le : c1 ≤ C₀ := le_trans (by linarith [show 0 ≤ c2 by positivity] : c1 ≤ c1 + c2) (le_max_left _ _)
          have hlog3_le : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1_le (Real.rpow_nonneg hL_pos.le _)) hlog3_le
        · have hr0 : rOf m = 0 := by
            rcases Nat.lt_trichotomy m 1 with h0 | h1 | hgt
            · have : m = 0 := by omega
              subst this; exact rOf_zero
            · rw [h1]; exact rOf_one
            · omega
          rw [hr0]
          simpa using hexp_ge1
      exact mul_le_mul (le_max_right _ _) hpow_bound (by positivity) hM_pos
  · intro m hm
    have hm4 : 4 ≤ m := le_trans (four_le_thresholdB1 cr) hm
    have hm2 : 2 ≤ m := by omega
    set L : ℝ := Real.log ((m : ℝ) + 2)
    have hL_gt1 : 1 < L := lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ m + 2)))
    have hL_pos : 0 < L := by linarith
    have hr_pos_nat : 1 ≤ rOf m := one_le_rOf hm2
    have hr_pos : (0 : ℝ) < rOf m := by exact_mod_cast hr_pos_nat
    have hm_le : (m : ℝ) + 2 ≤ 2 * m := by exact_mod_cast (by omega : m + 2 ≤ 2 * m)
    have hL_le : L ≤ Real.log (2 * m) := Real.log_le_log (by positivity) hm_le
    have hlog2m : Real.log (2 * m) = Real.log 2 + Real.log m := by
      rw [Real.log_mul (by norm_num) (by exact_mod_cast (by omega : m ≠ 0))]
    have hlogm_le : Real.log m ≤ ((Nat.log 2 m : ℝ) + 1) * Real.log 2 :=
      real_log_le_natLog2 (by omega)
    have hnat_lt : (Nat.log 2 m : ℝ) + 1 ≤ (rOf m + 1 : ℝ) ^ 3 := by
      exact_mod_cast lt_cubeRoot_succ_pow (Nat.log 2 m)
    have hr_ge1 : (1 : ℝ) ≤ (rOf m : ℝ) := by exact_mod_cast hr_pos_nat
    have hr1_le : (rOf m : ℝ) + 1 ≤ 2 * (rOf m : ℝ) := by linarith
    have hnat_le8 : (Nat.log 2 m : ℝ) + 1 ≤ 8 * (rOf m : ℝ) ^ 3 := by
      calc (Nat.log 2 m : ℝ) + 1 ≤ (rOf m + 1 : ℝ) ^ 3 := hnat_lt
        _ ≤ (2 * (rOf m : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hr1_le 3
        _ = 8 * (rOf m : ℝ) ^ 3 := by ring
    have hL_le_r3 : L ≤ 10 * Real.log 2 * (rOf m : ℝ) ^ 3 := by
      have h1 : 1 ≤ (rOf m : ℝ) ^ 3 := by
        have : (1 : ℝ) ≤ (rOf m : ℝ) := by exact_mod_cast hr_pos_nat
        nlinarith
      calc L ≤ Real.log 2 + ((Nat.log 2 m : ℝ) + 1) * Real.log 2 := by linarith
        _ ≤ Real.log 2 + (8 * (rOf m : ℝ) ^ 3) * Real.log 2 := by gcongr
        _ ≤ 2 * Real.log 2 * (rOf m : ℝ) ^ 3 + 8 * Real.log 2 * (rOf m : ℝ) ^ 3 := by nlinarith [hlog2.le]
        _ = 10 * Real.log 2 * (rOf m : ℝ) ^ 3 := by ring
    have hr_ge : (L / (10 * Real.log 2)) ^ (1 / 3 : ℝ) ≤ (rOf m : ℝ) := by
      have hdiv : L / (10 * Real.log 2) ≤ (rOf m : ℝ) ^ 3 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hpow_eq : ((L / (10 * Real.log 2)) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = L / (10 * Real.log 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (by positivity) _) hr_pos.le (by norm_num : 3 ≠ 0), hpow_eq]
      exact hdiv
    have hL_div_r : K / (rOf m : ℝ) * L ≤ c2 * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by
      have h1 : L / (rOf m : ℝ) ≤ (10 * Real.log 2) ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
        calc L / (rOf m : ℝ)
            ≤ L / (L / (10 * Real.log 2)) ^ (1 / 3 : ℝ) := by
              apply div_le_div_of_nonneg_left hL_pos.le (Real.rpow_pos_of_pos (by positivity) _) hr_ge
          _ = (10 * Real.log 2) ^ (1 / 3 : ℝ) * (L / L ^ (1 / 3 : ℝ)) := by
              rw [Real.div_rpow hL_pos.le (by positivity)]
              have hp1 : 0 < (10 * Real.log 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
              have hp2 : 0 < L ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hL_pos _
              field_simp
          _ = (10 * Real.log 2) ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
              congr 1
              conv_lhs => lhs; rw [← Real.rpow_one L]
              rw [← Real.rpow_sub hL_pos]
              congr 1; norm_num
      have hlog3_le : Real.log 3 ≤ Real.log (L + 2) := Real.log_le_log (by norm_num) (by linarith)
      calc K / (rOf m : ℝ) * L = K * (L / (rOf m : ℝ)) := by ring
        _ ≤ K * ((10 * Real.log 2) ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hK.le
        _ = c2 * Real.log 3 * L ^ (2 / 3 : ℝ) := by
          dsimp [c2]
          have : Real.log 3 ≠ 0 := hlog3.ne'
          field_simp
        _ ≤ c2 * Real.log (L + 2) * L ^ (2 / 3 : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hlog3_le (by positivity)
          · exact Real.rpow_nonneg hL_pos.le _
        _ = c2 * L ^ (2 / 3 : ℝ) * Real.log (L + 2) := by ring
    have hpow1 : ((m : ℝ) + 2) ^ (K / (rOf m : ℝ)) = Real.exp (K / (rOf m : ℝ) * L) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      dsimp [L]
      rw [mul_comm]
    have hpow2 := hr_bound m hm2
    rw [hpow1]
    calc Real.exp (K / (rOf m : ℝ) * L) * L ^ (K * (rOf m : ℝ) ^ 2)
        ≤ Real.exp (c2 * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) *
            Real.exp (c1 * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
          exact mul_le_mul (Real.exp_le_exp.mpr hL_div_r) hpow2 (Real.rpow_nonneg hL_pos.le _) (Real.exp_pos _).le
      _ = Real.exp ((c1 + c2) * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
          rw [← Real.exp_add]
          congr 1; ring
      _ ≤ Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2)) := by
          apply Real.exp_le_exp.mpr
          have hle_C : c1 + c2 ≤ C₀ := le_max_left _ _
          have hlog_nonneg : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle_C (Real.rpow_nonneg hL_pos.le _)) hlog_nonneg

/-! ### Tendsto o(1) exponent helper -/

/-- `(log(m+2))^{2/3} * log(log(m+2)+2) / log(m+2) → 0` as `m → ∞`, so the
`exp(O(log^{2/3} m log log m))` factor is `m^{o(1)}`. -/
lemma tendsto_b1_exponent_div_log :
    Tendsto (fun m : ℕ =>
      (Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2)) /
        Real.log ((m : ℝ) + 2)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ => Real.log ((m : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hlittle := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).tendsto_div_nhds_zero
  have hcomp : Tendsto (fun L : ℝ => Real.log (L + 2) / L ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
    have hshift := hlittle.comp (tendsto_atTop_add_const_right _ 2 tendsto_id)
    have hratio : Tendsto (fun L : ℝ => ((L + 2) ^ (1 / 3 : ℝ)) / L ^ (1 / 3 : ℝ)) atTop (𝓝 1) := by
      have h1 : ∀ᶠ L : ℝ in atTop, ((L + 2) ^ (1 / 3 : ℝ)) / L ^ (1 / 3 : ℝ) = (1 + 2 / L) ^ (1 / 3 : ℝ) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
        rw [← Real.div_rpow (by linarith) hL.le]
        congr 1
        field_simp
      rw [tendsto_congr' h1]
      have hlim0 : Tendsto (fun L : ℝ => 1 + 2 / L) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
      have hlim : Tendsto (fun L : ℝ => 1 + 2 / L) atTop (𝓝 1) := by
        simpa using hlim0
      have hrp : ContinuousAt (fun x : ℝ => x ^ (1 / 3 : ℝ)) 1 :=
        Real.continuousAt_rpow_const (1 : ℝ) (1 / 3 : ℝ) (Or.inl (by norm_num))
      simpa [Function.comp_def] using hrp.tendsto.comp hlim
    have hprod := hshift.mul hratio
    simp only [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hpos : 0 < (L + 2) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    dsimp only [Function.comp_def, id_eq]
    rw [div_mul_div_cancel₀ hpos.ne']
  refine (hcomp.comp hlog).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  set L : ℝ := Real.log ((m : ℝ) + 2)
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < m + 2))
  dsimp only [Function.comp_def]
  have hpow : L ^ (1 : ℝ) = L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hL_pos]
    norm_num
  show Real.log (L + 2) / L ^ (1 / 3 : ℝ) = L ^ (2 / 3 : ℝ) * Real.log (L + 2) / L
  conv_rhs => rhs; rw [← Real.rpow_one L, hpow]
  have hp1 : 0 < L ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hL_pos _
  have hp2 : 0 < L ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hL_pos _
  field_simp

/-! ### Theorem B.1 and generalized `ε`-version -/

/-- Expander decomposition model: invokes `citedOut` on valid loopless graphs with
`thr ≤ G.m`, and falls back to connected components `compLabels G` below `thr`. -/
@[expose] noncomputable def decompModel (citedOut : ℕ → ℕ → Graph → List ℕ) (thr : ℕ)
    (a b : ℕ) (G : Graph) : List ℕ :=
  letI := Classical.propDecidable
  if G.IsValid ∧ G.IsLoopless ∧ 1 ≤ a ∧ a ≤ b ∧ thr ≤ G.m then
    citedOut a b G
  else
    compLabels G

/-- Explicit operation count of `decompModel`: charges `citedCost a b G + G.n + G.m` for the
cited Word-RAM decomposition and graph encoding when `thr ≤ G.m`, and
`G.n + G.m + G.n * G.m` for the `compLabels` relaxation fallback below `thr`. -/
@[expose] noncomputable def decompModelCost (citedCost : ℕ → ℕ → Graph → ℕ) (thr : ℕ)
    (a b : ℕ) (G : Graph) : ℕ :=
  letI := Classical.propDecidable
  if G.IsValid ∧ G.IsLoopless ∧ 1 ≤ a ∧ a ≤ b ∧ thr ≤ G.m then
    citedCost a b G + G.n + G.m
  else
    G.n + G.m + G.n * G.m

/-- Generalized Theorem B.1 for any rational `ε = a / b` (`1 ≤ a ≤ b`):
given `Cited.ExpanderDecomposition`, there exist constants `K, cr, C₀, K_cost > 0`, a Word-RAM
program `P`, word-size constant `c_w`, and cited witness functions `(citedOut, citedCost)` such that
for any valid loopless `G` and `1 ≤ a ≤ b`, `label := decompModel citedOut (thresholdB1 cr) a b G`
is a `((a : ℝ) / b, phiB1 K cr a b G.m)`-expander decomposition of `G`, the number of inter-part
edges is at most `((a : ℝ) / b) * G.m`, and the defined operation count
`decompModelCost citedCost (thresholdB1 cr) a b G` is bounded by
`K_cost * (G.n + (b / a)^2 * (G.m + 2) * exp(C₀ * log(G.m+2)^{2/3} * log(log(G.m+2)+2)))`. -/
theorem expanderDecomp_of_cited (hDec : Cited.ExpanderDecomposition) :
    ∃ (K cr C₀ K_cost : ℝ) (P : WordRAM.Program) (c_w : ℕ)
      (citedOut : ℕ → ℕ → Graph → List ℕ) (citedCost : ℕ → ℕ → Graph → ℕ),
      0 < K ∧ 0 < cr ∧ 0 < C₀ ∧ 0 < K_cost ∧
      (∀ (a b : ℕ) (G : Graph), G.IsValid → G.IsLoopless → 1 ≤ a → a ≤ b →
        thresholdB1 cr ≤ G.m →
        WordRAM.RunsTo (WordRAM.wordSize c_w (G.encode ++ [a, b, rOf G.m])) P
          (G.encode ++ [a, b, rOf G.m]) (fun _ => false) (citedOut a b G) (citedCost a b G) ∧
        (citedCost a b G : ℝ) ≤ K * (G.n + ((G.m : ℝ) + 2) ^ (1 + K / rOf G.m) *
          Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) / ((a : ℝ) / b) ^ 2)) ∧
      ∀ (a b : ℕ) (G : Graph), G.IsValid → G.IsLoopless → 1 ≤ a → a ≤ b →
        let label := decompModel citedOut (thresholdB1 cr) a b G
        let cost := decompModelCost citedCost (thresholdB1 cr) a b G
        IsExpanderDecomposition G ((a : ℝ) / b) (phiB1 K cr a b G.m) label ∧
        ((G.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
          ((a : ℝ) / b) * G.m ∧
        (cost : ℝ) ≤
          K_cost * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by
  classical
  rcases hDec with ⟨K, cr, P, c, hK, hcr, hspec⟩
  obtain ⟨C₀, hC₀_pos, _, hC₀_mul⟩ := subpoly_exp_bounds hK hcr
  let citedOut : ℕ → ℕ → Graph → List ℕ := fun a b G =>
    if h : G.IsValid ∧ G.IsLoopless ∧ 1 ≤ a ∧ a ≤ b ∧ thresholdB1 cr ≤ G.m then
      let hr := rOf_le_cr_log hcr h.2.2.2.2
      Classical.choose (hspec G a b (rOf G.m) h.1 h.2.1 h.2.2.1 h.2.2.2.1 hr.1 hr.2 (fun _ => false))
    else []
  let citedCost : ℕ → ℕ → Graph → ℕ := fun a b G =>
    if h : G.IsValid ∧ G.IsLoopless ∧ 1 ≤ a ∧ a ≤ b ∧ thresholdB1 cr ≤ G.m then
      let hr := rOf_le_cr_log hcr h.2.2.2.2
      Classical.choose (Classical.choose_spec
        (hspec G a b (rOf G.m) h.1 h.2.1 h.2.2.1 h.2.2.2.1 hr.1 hr.2 (fun _ => false)))
    else 0
  have hrun_spec : ∀ a b G (h : G.IsValid ∧ G.IsLoopless ∧ 1 ≤ a ∧ a ≤ b ∧ thresholdB1 cr ≤ G.m),
      WordRAM.RunsTo (WordRAM.wordSize c (G.encode ++ [a, b, rOf G.m])) P
        (G.encode ++ [a, b, rOf G.m]) (fun _ => false) (citedOut a b G) (citedCost a b G) ∧
      IsExpanderDecomposition G ((a : ℝ) / b)
        (((a : ℝ) / b) / (K * Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2)))
        (citedOut a b G) ∧
      (citedCost a b G : ℝ) ≤ K * (G.n + ((G.m : ℝ) + 2) ^ (1 + K / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) / ((a : ℝ) / b) ^ 2) := by
    intro a b G h
    have hout : citedOut a b G = Classical.choose (hspec G a b (rOf G.m) h.1 h.2.1 h.2.2.1 h.2.2.2.1
        (rOf_le_cr_log hcr h.2.2.2.2).1 (rOf_le_cr_log hcr h.2.2.2.2).2 (fun _ => false)) := by
      dsimp only [citedOut]
      exact dite_eq_left_of_eq_true (eq_true h)
    have hcost_eq : citedCost a b G = Classical.choose (Classical.choose_spec (hspec G a b (rOf G.m)
        h.1 h.2.1 h.2.2.1 h.2.2.2.1
        (rOf_le_cr_log hcr h.2.2.2.2).1 (rOf_le_cr_log hcr h.2.2.2.2).2 (fun _ => false))) := by
      dsimp only [citedCost]
      exact dite_eq_left_of_eq_true (eq_true h)
    rw [hout, hcost_eq]
    exact Classical.choose_spec (Classical.choose_spec (hspec G a b (rOf G.m) h.1 h.2.1 h.2.2.1
      h.2.2.2.1 (rOf_le_cr_log hcr h.2.2.2.2).1 (rOf_le_cr_log hcr h.2.2.2.2).2 (fun _ => false)))
  let K_cost : ℝ := max (K + 1) ((thresholdB1 cr : ℝ) + 1)
  have hK_cost : 0 < K_cost := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨K, cr, C₀, K_cost, P, c, citedOut, citedCost, hK, hcr, hC₀_pos, hK_cost, ?_, ?_⟩
  · intro a b G hGv hGl ha hab hm
    have hprop := hrun_spec a b G ⟨hGv, hGl, ha, hab, hm⟩
    exact ⟨hprop.1, hprop.2.2⟩
  · intro a b G hGv hGl ha hab
    dsimp only [decompModel, decompModelCost]
    have hL_pos : 0 < Real.log ((G.m : ℝ) + 2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) G.m])
    have hexp_ge1 : 1 ≤ Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
      apply Real.one_le_exp
      have : 0 ≤ Real.log (Real.log ((G.m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
      positivity
    have hba_ge1 : (1 : ℝ) ≤ (b : ℝ) / a := by
      have hapos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
      have hle : (a : ℝ) ≤ b := by exact_mod_cast hab
      rwa [one_le_div hapos]
    have hm_le_term : (G.m : ℝ) ≤ ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
        Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
      calc (G.m : ℝ) ≤ (G.m : ℝ) + 2 := by linarith
        _ = 1 * ((G.m : ℝ) + 2) * 1 := by ring
        _ ≤ ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
            apply mul_le_mul _ hexp_ge1 (by norm_num) (by positivity)
            exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    by_cases hm : thresholdB1 cr ≤ G.m
    · have hcond : G.IsValid ∧ G.IsLoopless ∧ 1 ≤ a ∧ a ≤ b ∧ thresholdB1 cr ≤ G.m :=
        ⟨hGv, hGl, ha, hab, hm⟩
      simp only [hcond, and_self, ↓reduceIte]
      have hprop := hrun_spec a b G hcond
      set out := citedOut a b G
      obtain ⟨_, hdecomp, hcost⟩ := hprop
      have hdecomp' : IsExpanderDecomposition G ((a : ℝ) / b) (phiB1 K cr a b G.m) out := by
        refine ⟨hdecomp.1, fun X hX => ?_, hdecomp.2.2⟩
        exact isConductanceExpanderOn_mono (phiB1_le_cor K cr a b G.m) (hdecomp.2.1 X hX)
      have hcut_edges : ((G.edges.filter fun e => decide (out.getD e.1 0 ≠ out.getD e.2 0)).length : ℝ) ≤
          ((a : ℝ) / b) * G.m := by
        have hsum := sum_cut_partsOf hGv out
        have hvol := vol_verts_of_isValid hGv
        have hle := hdecomp.2.2
        rw [hvol] at hle
        have hsum_r : (∑ X ∈ partsOf G out, (G.cut X : ℝ)) =
            2 * ((G.edges.filter fun e => decide (out.getD e.1 0 ≠ out.getD e.2 0)).length : ℝ) := by
          exact_mod_cast hsum
        rw [hsum_r] at hle
        push_cast at hle
        linarith
      refine ⟨hdecomp', hcut_edges, ?_⟩
      have hpow_split : ((G.m : ℝ) + 2) ^ (1 + K / (rOf G.m : ℝ)) =
          ((G.m : ℝ) + 2) * ((G.m : ℝ) + 2) ^ (K / (rOf G.m : ℝ)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_one]
      have hcost1 : ((G.m : ℝ) + 2) ^ (1 + K / (rOf G.m : ℝ)) *
          Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) / ((a : ℝ) / b) ^ 2 ≤
          ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
        rw [hpow_split, div_eq_mul_inv]
        have hinv_sq : (((a : ℝ) / b) ^ 2)⁻¹ = ((b : ℝ) / a) ^ 2 := by
          field_simp
        rw [hinv_sq]
        have hmul := hC₀_mul G.m hm
        calc ((G.m : ℝ) + 2) * ((G.m : ℝ) + 2) ^ (K / (rOf G.m : ℝ)) *
              Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) * ((b : ℝ) / a) ^ 2
            = ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
                (((G.m : ℝ) + 2) ^ (K / (rOf G.m : ℝ)) *
                  Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2)) := by ring
          _ ≤ ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
                Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                  Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
                exact mul_le_mul_of_nonneg_left hmul (by positivity)
      have hcited_le : (citedCost a b G : ℝ) ≤
          K * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2))) :=
        le_trans hcost (mul_le_mul_of_nonneg_left (add_le_add le_rfl hcost1) hK.le)
      have hK1_le : K + 1 ≤ K_cost := le_max_left _ _
      have hrhs_nn : 0 ≤ (G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
          Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by positivity
      calc ((citedCost a b G + G.n + G.m : ℕ) : ℝ)
          = (citedCost a b G : ℝ) + ((G.n : ℝ) + (G.m : ℝ)) := by push_cast; ring
        _ ≤ K * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) +
            1 * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by linarith
        _ = (K + 1) * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by ring
        _ ≤ K_cost * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) :=
            mul_le_mul_of_nonneg_right hK1_le hrhs_nn
    · have hcond : ¬ (G.IsValid ∧ G.IsLoopless ∧ 1 ≤ a ∧ a ≤ b ∧ thresholdB1 cr ≤ G.m) := by
        intro h; exact hm h.2.2.2.2
      simp only [hcond, ↓reduceIte]
      have hlen : (compLabels G).length = G.n := compLabels_length G
      have hexp_part : ∀ X ∈ partsOf G (compLabels G),
          G.IsConductanceExpanderOn X (phiB1 K cr a b G.m) := by
        intro X hX
        apply isConductanceExpanderOn_mono (min_le_left _ _)
        intro S hSX hSne hSXne
        have hcut1 : (1 : ℝ) ≤ G.cutIn X S := by
          exact_mod_cast cutIn_ge_one_of_part_compLabels hGv hX hSX hSne hSXne
        have hsum_v : G.volIn X S + G.volIn X (X \ S) = 2 * (G.inside X).length :=
          volIn_add_volIn_sdiff G X S hSX
        have hmin_le : min (G.volIn X S) (G.volIn X (X \ S)) ≤ G.m := by
          have hlen_m := inside_length_le_m G X
          omega
        have hm_lt : G.m < thresholdB1 cr := by omega
        have hmin_r : min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) ≤ (thresholdB1 cr : ℝ) + 1 := by
          have : (min (G.volIn X S) (G.volIn X (X \ S)) : ℝ) ≤ (thresholdB1 cr : ℝ) + 1 := by
            exact_mod_cast (by omega : min (G.volIn X S) (G.volIn X (X \ S)) ≤ thresholdB1 cr + 1)
          exact_mod_cast this
        calc (1 / ((thresholdB1 cr : ℝ) + 1)) * min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ)
            ≤ (1 / ((thresholdB1 cr : ℝ) + 1)) * ((thresholdB1 cr : ℝ) + 1) := by
              apply mul_le_mul_of_nonneg_left hmin_r (by positivity)
          _ = 1 := by field_simp
          _ ≤ G.cutIn X S := hcut1
      have hsum_cut : (∑ X ∈ partsOf G (compLabels G), (G.cut X : ℝ)) ≤
          ((a : ℝ) / b) * (G.vol G.verts : ℝ) := by
        have hzero : ∑ X ∈ partsOf G (compLabels G), (G.cut X : ℝ) = 0 := by
          apply Finset.sum_eq_zero
          intro X hX
          simp [cut_part_compLabels_eq_zero hGv hX]
        rw [hzero]
        positivity
      have hcut_edges : ((G.edges.filter fun e =>
          decide ((compLabels G).getD e.1 0 ≠ (compLabels G).getD e.2 0)).length : ℝ) ≤
          ((a : ℝ) / b) * G.m := by
        have hsum := sum_cut_partsOf hGv (compLabels G)
        have hzero_cut : ∑ X ∈ partsOf G (compLabels G), G.cut X = 0 := by
          apply Finset.sum_eq_zero
          intro X hX
          exact cut_part_compLabels_eq_zero hGv hX
        rw [hzero_cut] at hsum
        have hlen_zero : (G.edges.filter fun e =>
            decide ((compLabels G).getD e.1 0 ≠ (compLabels G).getD e.2 0)).length = 0 := by omega
        rw [hlen_zero]
        simp only [Nat.cast_zero]
        positivity
      refine ⟨⟨hlen, hexp_part, hsum_cut⟩, hcut_edges, ?_⟩
      have hm_lt : G.m ≤ thresholdB1 cr := by omega
      have hnat_le : G.n + G.m + G.n * G.m ≤ (thresholdB1 cr + 1) * G.n + G.m := by
        have hmul : G.n * G.m ≤ G.n * thresholdB1 cr := Nat.mul_le_mul_left G.n hm_lt
        nlinarith
      have hreal_le : ((G.n + G.m + G.n * G.m : ℕ) : ℝ) ≤
          ((thresholdB1 cr : ℝ) + 1) * (G.n : ℝ) + (G.m : ℝ) := by
        exact_mod_cast hnat_le
      have hthr_ge1 : (1 : ℝ) ≤ (thresholdB1 cr : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) (thresholdB1 cr)
        linarith
      have hthr_le : (thresholdB1 cr : ℝ) + 1 ≤ K_cost := le_max_right _ _
      calc ((G.n + G.m + G.n * G.m : ℕ) : ℝ)
          ≤ ((thresholdB1 cr : ℝ) + 1) * (G.n : ℝ) + (G.m : ℝ) := hreal_le
        _ ≤ ((thresholdB1 cr : ℝ) + 1) * (G.n : ℝ) +
              ((thresholdB1 cr : ℝ) + 1) * (((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
                Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                  Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by
              have : (G.m : ℝ) ≤ ((thresholdB1 cr : ℝ) + 1) * (G.m : ℝ) :=
                le_mul_of_one_le_left (Nat.cast_nonneg _) hthr_ge1
              nlinarith
        _ = ((thresholdB1 cr : ℝ) + 1) * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by ring
        _ ≤ K_cost * ((G.n : ℝ) + ((b : ℝ) / a) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) :=
            mul_le_mul_of_nonneg_right hthr_le (by positivity)

/-- **Theorem B.1** (page 49), derived from `Cited.ExpanderDecomposition`:
on any valid loopless graph `G` with `m` edges, `decompModel citedOut (thresholdB1 cr) 1 4 G`
computes a partition into `φ(m)`-expanders with at most `m / 4` inter-part edges, where
`1 / φ(m) ≤ C₁ * exp(C₀ * log(m+2)^{2/3} * log(log(m+2)+2))` (so `φ(m) = 1 / exp(O(log^{2/3} m log log m))`)
and the defined operation count `decompModelCost citedCost (thresholdB1 cr) 1 4 G` is
`O(n + m · exp(O(log^{2/3} m log log m)))`. -/
theorem theorem_B_1 (hDec : Cited.ExpanderDecomposition) :
    ∃ (φ : ℕ → ℝ) (C₀ C₁ cr : ℝ) (P : WordRAM.Program) (c_w : ℕ)
      (citedOut : ℕ → ℕ → Graph → List ℕ) (citedCost : ℕ → ℕ → Graph → ℕ),
      0 < C₀ ∧ 0 < C₁ ∧ 0 < cr ∧
      (∀ m : ℕ, 0 < φ m ∧ φ m ≤ 1 ∧
        1 / φ m ≤ C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2))) ∧
      (∀ G : Graph, G.IsValid → G.IsLoopless → thresholdB1 cr ≤ G.m →
        WordRAM.RunsTo (WordRAM.wordSize c_w (G.encode ++ [1, 4, rOf G.m])) P
          (G.encode ++ [1, 4, rOf G.m]) (fun _ => false) (citedOut 1 4 G) (citedCost 1 4 G)) ∧
      (∀ G : Graph, G.IsValid → G.IsLoopless →
        let label := decompModel citedOut (thresholdB1 cr) 1 4 G
        let cost := decompModelCost citedCost (thresholdB1 cr) 1 4 G
        label.length = G.n ∧
        (∀ X ∈ partsOf G label, G.IsConductanceExpanderOn X (φ G.m)) ∧
        ((G.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
          (G.m : ℝ) / 4 ∧
        (cost : ℝ) ≤
          C₁ * ((G.n : ℝ) + ((G.m : ℝ) + 2) *
            Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((G.m : ℝ) + 2) + 2)))) := by
  obtain ⟨K, cr, C₀, K_cost, P, c_w, citedOut, citedCost, hK, hcr, hC₀_pos, hK_cost, hcited, hspec⟩ :=
    expanderDecomp_of_cited hDec
  obtain ⟨C₀', hC₀'_pos, hphi_bound, _⟩ := subpoly_exp_bounds hK hcr
  let C_exp := max C₀ C₀'
  let C₁ := max (max ((thresholdB1 cr : ℝ) + 1) (K * 4)) (16 * K_cost)
  have hC_exp_pos : 0 < C_exp := lt_of_lt_of_le hC₀_pos (le_max_left _ _)
  have hC₁_pos : 0 < C₁ := by positivity
  refine ⟨fun m => phiB1 K cr 1 4 m, C_exp, C₁, cr, P, c_w, citedOut, citedCost,
    hC_exp_pos, hC₁_pos, hcr, ?_, ?_, ?_⟩
  · intro m
    refine ⟨phiB1_pos hK hcr (by norm_num) (by norm_num) m, phiB1_le_one K cr 1 4 m, ?_⟩
    have h1 := hphi_bound 1 4 m (by norm_num) (by norm_num)
    have hL_nonneg : 0 ≤ Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((m : ℝ) + 2) + 2) := by
      have hL : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
      have hLL : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
      exact mul_nonneg (Real.rpow_nonneg hL _) hLL
    have hexp_le : Real.exp (C₀' * (Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((m : ℝ) + 2) + 2))) ≤
        Real.exp (C_exp * (Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2))) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL_nonneg)
    have hcoeff : max ((thresholdB1 cr : ℝ) + 1) (K * (4 : ℕ) / (1 : ℕ)) ≤ C₁ := by
      dsimp [C₁]
      norm_num
    have hexp_nonneg : 0 ≤ Real.exp (C₀' * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((m : ℝ) + 2) + 2)) := (Real.exp_pos _).le
    calc 1 / phiB1 K cr 1 4 m
        ≤ max ((thresholdB1 cr : ℝ) + 1) (K * (4 : ℕ) / (1 : ℕ)) *
            Real.exp (C₀' * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
              Real.log (Real.log ((m : ℝ) + 2) + 2)) := h1
      _ ≤ C₁ * Real.exp (C_exp * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((m : ℝ) + 2) + 2)) := by
          apply mul_le_mul hcoeff (by simpa [mul_assoc] using hexp_le) hexp_nonneg hC₁_pos.le
  · intro G hGv hGl hm
    exact (hcited 1 4 G hGv hGl (by norm_num) (by norm_num) hm).1
  · intro G hGv hGl
    obtain ⟨hdec, hcut, hcost⟩ := hspec 1 4 G hGv hGl (by norm_num) (by norm_num)
    refine ⟨hdec.1, hdec.2.1, ?_, ?_⟩
    · have : ((1 : ℕ) : ℝ) / (4 : ℕ) * (G.m : ℝ) = (G.m : ℝ) / 4 := by norm_num; ring
      linarith
    · have hL_nonneg : 0 ≤ Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((G.m : ℝ) + 2) + 2) := by
        have hL : 0 ≤ Real.log ((G.m : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) G.m])
        have hLL : 0 ≤ Real.log (Real.log ((G.m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
        exact mul_nonneg (Real.rpow_nonneg hL _) hLL
      have hexp_le : Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((G.m : ℝ) + 2) + 2)) ≤
          Real.exp (C_exp * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
        apply Real.exp_le_exp.mpr
        rw [mul_assoc C₀, mul_assoc C_exp]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL_nonneg
      calc (decompModelCost citedCost (thresholdB1 cr) 1 4 G : ℝ)
          ≤ K_cost * ((G.n : ℝ) + ((4 : ℕ) / (1 : ℕ)) ^ 2 * ((G.m : ℝ) + 2) *
              Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := hcost
        _ ≤ 16 * K_cost * ((G.n : ℝ) + ((G.m : ℝ) + 2) *
              Real.exp (C_exp * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by
            have h16 : (((4 : ℕ) : ℝ) / (1 : ℕ)) ^ 2 = 16 := by norm_num
            rw [h16]
            have hsub : (G.n : ℝ) + 16 * ((G.m : ℝ) + 2) *
                Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                  Real.log (Real.log ((G.m : ℝ) + 2) + 2)) ≤
                16 * ((G.n : ℝ) + ((G.m : ℝ) + 2) *
                  Real.exp (C_exp * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                    Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by
              have hm2_nonneg : 0 ≤ (G.m : ℝ) + 2 := by positivity
              have hn_nonneg : 0 ≤ (G.n : ℝ) := Nat.cast_nonneg _
              nlinarith [mul_le_mul_of_nonneg_left hexp_le hm2_nonneg]
            nlinarith
        _ ≤ C₁ * ((G.n : ℝ) + ((G.m : ℝ) + 2) *
              Real.exp (C_exp * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2))) := by
            apply mul_le_mul_of_nonneg_right (le_max_right _ _)
            positivity

end MinCostFlow.Expander
