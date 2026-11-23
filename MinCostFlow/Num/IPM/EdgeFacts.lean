module

public import MinCostFlow.IPM.Definitions
public import MinCostFlow.Num.ApproximationFacts
import Mathlib.Tactic

/-!
# Scalar error bounds for IPM edge numbers

Definition 4.2 of Chen et al. (page 24) uses two negative slack powers.
Their dyadic input range bounds both powers, including the lower bound needed
to compare absolute gradient errors with an edge length. Relative errors on
the two powers add without increasing their common relative bound.
-/

public section
namespace MinCostFlow.Num.IPM

/-- An additive relative error of `ε/2` implies the paper's multiplicative
comparison with factor `1+ε`, for `0<ε≤1`. -/
theorem scalarApprox_of_relative_error {x y ε : ℝ} (hy : 0<y)
    (hε0 : 0<ε) (hε1 : ε≤1) (herr : |x-y|≤(ε/2)*y) :
    MinCostFlow.IPM.ScalarApprox (1+ε) x y := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp herr
  have hprod := mul_le_mul_of_nonneg_right hε1 (le_of_lt hy)
  have hx : 0<x := by nlinarith only [hlo,hprod,hy]
  have hb : 0<1+ε := by linarith only [hε0]
  have hinv : (1+ε)⁻¹≤1-ε/2 := by
    rw [← one_div]
    apply (div_le_iff₀ hb).mpr
    have hh := mul_nonneg (le_of_lt hε0) (sub_nonneg.mpr hε1)
    nlinarith only [hh]
  refine ⟨hx,hy,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hinv (le_of_lt hy)
    nlinarith only [hh,hlo]
  · have hh := mul_nonneg (le_of_lt hε0) (le_of_lt hy)
    nlinarith only [hhi,hh]

/-- The exact slack power lower bound in Definition 4.2 (page 24), before
rounding. This is the scale used for the gradient's absolute error. -/
theorem slack_power_bounds {s a : ℝ} {E : ℕ}
    (hs0 : 1/(2:ℝ)^E≤s) (hs1 : s≤(2:ℝ)^E) (ha0 : 0≤a) (ha1 : a≤1) :
    Real.rpow 2 (-(1+a)*(E:ℝ))≤Real.rpow s (-1-a) ∧
    Real.rpow s (-1-a)≤Real.rpow 2 ((1+a)*(E:ℝ)) := by
  have hspos : 0<s := lt_of_lt_of_le (by positivity) hs0
  have hexp : -1-a≤0 := by linarith only [ha0]
  have hlow := Real.rpow_le_rpow_of_nonpos hspos hs1 hexp
  have hhigh := Real.rpow_le_rpow_of_nonpos
    (show (0:ℝ)<1/(2:ℝ)^E by positivity) hs0 hexp
  have hleft : ((2:ℝ)^E)^(-1-a)=Real.rpow 2 (-(1+a)*(E:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hright : (1/(2:ℝ)^E)^(-1-a)=Real.rpow 2 ((1+a)*(E:ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (by positivity),Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
      Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow]
    congr 1
    ring
  simp only [Real.rpow_eq_pow] at hleft hright ⊢
  exact ⟨hleft ▸ hlow,hright ▸ hhigh⟩

/-- Uniform dyadic bounds on both powers, valid for every exponent in `[0,1]`. -/
theorem slack_power_dyadic_bounds {s a : ℝ} {E : ℕ}
    (hs0 : 1/(2:ℝ)^E≤s) (hs1 : s≤(2:ℝ)^E) (ha0 : 0≤a) (ha1 : a≤1) :
    1/(2:ℝ)^(2*E)≤Real.rpow s (-1-a) ∧ Real.rpow s (-1-a)≤(2:ℝ)^(2*E) := by
  obtain ⟨hlo,hhi⟩ := slack_power_bounds hs0 hs1 ha0 ha1
  have hE : (0:ℝ)≤E := Nat.cast_nonneg E
  have hl := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    (show -((2*E:ℕ):ℝ)≤-(1+a)*(E:ℝ) by push_cast; nlinarith only [ha1,hE])
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    (show (1+a)*(E:ℝ)≤((2*E:ℕ):ℝ) by push_cast; nlinarith only [ha1,hE])
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast] at hl
  rw [Real.rpow_natCast] at hh
  simp only [Real.rpow_eq_pow] at hlo hhi ⊢
  exact ⟨by simpa only [one_div] using le_trans hl hlo,le_trans hhi hh⟩

/-- The sum of the two approximate positive powers meets the multiplicative
length comparison of Definition 4.2 (page 24). -/
theorem length_scalarApprox {u v u' v' ε : ℝ}
    (hu : 0<u) (hv : 0<v) (hε0 : 0<ε) (hε1 : ε≤1)
    (hu' : |u'-u|≤(ε/2)*u) (hv' : |v'-v|≤(ε/2)*v) :
    MinCostFlow.IPM.ScalarApprox (1+ε) (u'+v') (u+v) :=
  scalarApprox_of_relative_error (add_pos hu hv) hε0 hε1 (relative_error_add hu' hv')

/-- Rounding each positive power with relative error at most one leaves
four times their common upper bound as a bound on the absolute sum. -/
theorem approximate_power_sum_bound {u v u' v' δ M : ℝ}
    (hu0 : 0≤u) (hv0 : 0≤v) (hu : u≤M) (hv : v≤M)
    (hδ0 : 0≤δ) (hδ1 : δ≤1)
    (heu : |u'-u|≤δ*u) (hev : |v'-v|≤δ*v) : |u'+v'|≤4*M := by
  obtain ⟨hulo,huhi⟩ := abs_le.mp heu
  obtain ⟨hvlo,hvhi⟩ := abs_le.mp hev
  have hdu := mul_le_mul_of_nonneg_right hδ1 hu0
  have hdv := mul_le_mul_of_nonneg_right hδ1 hv0
  apply abs_le.mpr
  constructor <;> linarith only [hulo,huhi,hvlo,hvhi,hdu,hdv,hu,hv,hu0,hv0]

/-- Scalar edge-length statements specialize directly to `IPM.lengths`. -/
theorem lengths_from_slacks (I : Instance) (a : ℝ) (f : Fin I.m→ℝ) (e : Fin I.m)
    {v b : ℝ}
    (hv : MinCostFlow.IPM.ScalarApprox b v
      (Real.rpow (((I.edge e).upper:ℝ)-f e) (-1-a)+
        Real.rpow (f e-((I.edge e).lower:ℝ)) (-1-a))) :
    MinCostFlow.IPM.ScalarApprox b v (MinCostFlow.IPM.lengths I a f e) := hv

end MinCostFlow.Num.IPM
