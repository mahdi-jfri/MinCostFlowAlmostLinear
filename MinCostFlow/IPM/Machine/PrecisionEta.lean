module

public import MinCostFlow.IPM.Machine.PrecisionParameters
public import MinCostFlow.Num.ApproximationFacts
import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Representable normalization parameters

The requested normalization must itself be stored in fixed-point form.
Rounding it once has a separate error from the data structure's returned
normalization. Two extra precision bits make this initial rounding error
at most one quarter of the requested normalization. Combining its interval
with the tighter epoch residual estimate retains the factor-four effective
step interval of Chen et al., arXiv:2203.00671v2, Lemma 9.3 (page 71).
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- A dyadic rounding unit is at most one quarter of a positive number
above the supplied lower endpoint. -/
theorem normalization_unit_le_quarter {eta : ℝ} {S P : ℕ}
    (heta : 1/(2:ℝ)^S ≤ eta) (hP : S+2 ≤ P) :
    1/(2:ℝ)^P ≤ eta/4 := by
  have hh : (2:ℝ)^(S+2) ≤ (2:ℝ)^P := pow_le_pow_right₀ (by norm_num) hP
  have hinv := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(2:ℝ)^(S+2)) hh
  have he : 1/(2:ℝ)^(S+2) = (1/(2:ℝ)^S)/4 := by rw [pow_add]; norm_num; ring
  rw [he] at hinv
  exact hinv.trans (div_le_div_of_nonneg_right heta (by norm_num))

/-- Rounding a positive normalization to the selected dyadic grid stays
within `[3 eta/4,5 eta/4]`. This proves a fitting representable choice
exists without assuming the exact real normalization is dyadic. -/
theorem normalization_rounding_exists {eta : ℝ} {h L S P : ℕ}
    (heta : 1/(2:ℝ)^S ≤ eta) (hetaUpper : eta ≤ 1)
    (hP : S+2 ≤ P) (hwidth : P+4 ≤ h*L) :
    ∃ actual : ℝ, ScalarFits h L P actual ∧
      (3/4:ℝ)*eta ≤ actual ∧ actual ≤ (5/4:ℝ)*eta := by
  let z : ℤ := ⌊eta*(2:ℝ)^P⌋
  let actual : ℝ := (z:ℝ)/(2:ℝ)^P
  have he : |actual-eta| ≤ 1/(2:ℝ)^P := Num.floor_scaled_error eta P
  have hu := normalization_unit_le_quarter heta hP
  have he' := he.trans hu
  have hpos : 0 < eta := lt_of_lt_of_le (by positivity) heta
  have hl := (abs_le.mp he').1
  have hh := (abs_le.mp he').2
  have habs : |actual| ≤ (2:ℝ)^1 := by
    apply abs_le.mpr
    constructor <;> norm_num <;> linarith only [hl,hh,hpos,hetaUpper]
  have hfit : Num.Fits h L z := Num.IPM.fits_of_scaled_bound (P:=P) (E:=1) (by omega) habs
  exact ⟨actual,⟨z,hfit,rfl⟩,by linarith only [hl],by linarith only [hh]⟩

/-- Three numerical factors still stay in the effective-step interval:
the tighter residual estimate, the requested dyadic normalization, and
the data structure's scalar rounding. -/
theorem normalization_three_factor_bounds {s r t : ℝ}
    (hs : (3/4:ℝ) ≤ s ∧ s ≤ 4/3)
    (hr : (1/2:ℝ) ≤ r ∧ r ≤ 2)
    (ht : (3/4:ℝ) ≤ t ∧ t ≤ 5/4) :
    (1/4:ℝ) ≤ s*(r*t) ∧ s*(r*t) ≤ 4 := by
  have hs0 : 0 ≤ s := (by norm_num : (0:ℝ) ≤ 3/4).trans hs.1
  have hr0 : 0 ≤ r := (by norm_num : (0:ℝ) ≤ 1/2).trans hr.1
  have ht0 : 0 ≤ t := (by norm_num : (0:ℝ) ≤ 3/4).trans ht.1
  have hrtlo := mul_le_mul hr.1 ht.1 (by norm_num : (0:ℝ) ≤ 3/4) hr0
  have hrthi := mul_le_mul hr.2 ht.2 ht0 (by norm_num : (0:ℝ) ≤ 2)
  have hlo := mul_le_mul hs.1 hrtlo (by norm_num : (0:ℝ) ≤ (1/2)*(3/4)) hs0
  have hhi := mul_le_mul hs.2 hrthi (mul_nonneg hr0 ht0) (by norm_num : (0:ℝ) ≤ 4/3)
  constructor <;> nlinarith only [hlo,hhi]

/-- The epoch's multiplicative residual estimate supplies the tighter
ratio interval used when normalization storage also incurs rounding. -/
theorem residual_ratio_three_fourths {stored current eps : ℝ}
    (heps : 0 ≤ eps) (hepsUpper : eps ≤ 1/3)
    (hr : ScalarApprox (1+eps) stored current) :
    (3/4:ℝ) ≤ stored/current ∧ stored/current ≤ 4/3 := by
  have hb : 0 < 1+eps := by linarith only [heps]
  have hinv : (3/4:ℝ) ≤ (1+eps)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hb).mpr
    linarith only [hepsUpper]
  constructor
  · apply (le_div_iff₀ hr.2.1).mpr
    exact (mul_le_mul_of_nonneg_right hinv hr.2.1.le).trans hr.2.2.1
  · apply (div_le_iff₀ hr.2.1).mpr
    exact hr.2.2.2.trans (mul_le_mul_of_nonneg_right
      (by linarith only [hepsUpper] : 1+eps ≤ 4/3) hr.2.1.le)

end MinCostFlow.IPM.Machine
