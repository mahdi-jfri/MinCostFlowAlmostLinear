module

public import MinCostFlow.Num.IPM.EdgeFacts
import Mathlib.Tactic

/-!
# Error budgets for an IPM gradient entry

Definition 4.2 of Chen et al. (page 24) has a reciprocal cost term and
two alpha-weighted powers. The reciprocal term has no factor of the edge
length, so its requested accuracy must cover the smallest possible length.
The power errors and the two fixed-point product roundings are then added.
-/

public section
namespace MinCostFlow.Num.IPM

/-- Errors from one approximate power and one rounded multiplication add.
The condition `0≤a≤1` ensures that alpha does not enlarge the power error. -/
theorem weighted_power_error {a u u' z δ t : ℝ}
    (ha0 : 0≤a) (ha1 : a≤1) (hu : 0≤u) (hδ : 0≤δ)
    (hp : |u'-u|≤δ*u) (hr : |z-a*u'|≤t) : |z-a*u|≤t+δ*u := by
  have haabs : |a|≤1 := by rwa [abs_of_nonneg ha0]
  calc
    |z-a*u| = |(z-a*u')+a*(u'-u)| := by congr 1; ring
    _ ≤ |z-a*u'|+|a*(u'-u)| := abs_add_le _ _
    _ ≤ t+δ*u := add_le_add hr (by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hp (abs_nonneg a))
        (mul_le_of_le_one_left (mul_nonneg hδ hu) haabs))

/-- Subtraction of two positive approximations has the same absolute
error budget as their sum. -/
theorem power_difference_error {u v u' v' δ : ℝ}
    (hu : |u'-u|≤δ*u) (hv : |v'-v|≤δ*v) :
    |(u'-v')-(u-v)|≤δ*(u+v) := by
  have ht : |(u'-v')-(u-v)|≤|u'-u|+|v'-v| := by
    have he : (u'-v')-(u-v)=(u'-u)+(-(v'-v)) := by ring
    rw [he]
    simpa only [abs_neg] using abs_add_le (u'-u) (-(v'-v))
  calc
    _ ≤ |u'-u|+|v'-v| := ht
    _ ≤ δ*u+δ*v := add_le_add hu hv
    _ = _ := by ring

/-- A rounded alpha-weighted difference combines its single rounding with
the errors in the two powers. -/
theorem barrier_error {a u v u' v' z δ unit : ℝ}
    (ha0 : 0≤a) (ha1 : a≤1) (hδ : 0≤δ) (hu0 : 0≤u) (hv0 : 0≤v)
    (hu : |u'-u|≤δ*u) (hv : |v'-v|≤δ*v)
    (hr : |z-a*(u'-v')|≤unit) :
    |z-(a*u-a*v)|≤unit+δ*(u+v) := by
  have hd := power_difference_error hu hv
  have habs : |a|≤1 := by rwa [abs_of_nonneg ha0]
  have ht : |a*((u'-v')-(u-v))|≤δ*(u+v) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg a)).trans
      (mul_le_of_le_one_left (mul_nonneg hδ (add_nonneg hu0 hv0)) habs)
  calc
    _ = |(z-a*(u'-v'))+a*((u'-v')-(u-v))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hr ht

/-- The difference of approximate positive powers is bounded by four times
their common upper bound, enough for exact signed subtraction. -/
theorem approximate_power_difference_bound {u v u' v' δ M : ℝ}
    (hu0 : 0≤u) (hv0 : 0≤v) (hu : u≤M) (hv : v≤M) (hδ1 : δ≤1)
    (heu : |u'-u|≤δ*u) (hev : |v'-v|≤δ*v) : |u'-v'|≤4*M := by
  obtain ⟨hulo,huhi⟩ := abs_le.mp heu
  obtain ⟨hvlo,hvhi⟩ := abs_le.mp hev
  have hdu := mul_le_mul_of_nonneg_right hδ1 hu0
  have hdv := mul_le_mul_of_nonneg_right hδ1 hv0
  apply abs_le.mpr
  constructor <;> linarith only [hulo,huhi,hvlo,hvhi,hdu,hdv,hu,hv,hu0,hv0]

/-- The absolute gradient error is measured in units of the edge length.
One quarter covers each source of error: the cost term, the two power
approximations together, and the two product roundings together. -/
theorem gradient_error {a u v u' v' au av t t' ε unit : ℝ}
    (ha0 : 0≤a) (ha1 : a≤1) (hu : 0≤u) (hv : 0≤v) (hε : 0≤ε)
    (hup : |u'-u|≤(ε/4)*u) (hvp : |v'-v|≤(ε/4)*v)
    (hau : |au-a*u'|≤unit) (hav : |av-a*v'|≤unit)
    (ht : |t'-t|≤(ε/4)*(u+v)) (hunit : unit≤(ε/8)*(u+v)) :
    |(t'+au-av)-(t+a*u-a*v)|≤ε*(u+v) := by
  have huerr := weighted_power_error ha0 ha1 hu (by positivity : 0≤ε/4) hup hau
  have hverr := weighted_power_error ha0 ha1 hv (by positivity : 0≤ε/4) hvp hav
  have hsum : |(t'+au-av)-(t+a*u-a*v)|≤|t'-t|+|au-a*u|+|av-a*v| := by
    calc
      _ = |((t'-t)+(au-a*u))-(av-a*v)| := by congr 1; ring
      _ ≤ |(t'-t)+(au-a*u)|+|av-a*v| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le ((t'-t)+(au-a*u)) (-(av-a*v)))
      _ ≤ _ := add_le_add (abs_add_le (t'-t) (au-a*u)) (le_refl |av-a*v|)
  have hnonneg : 0≤ε*(u+v) := mul_nonneg hε (add_nonneg hu hv)
  linarith only [hsum,huerr,hverr,ht,hunit,hnonneg]

/-- The reciprocal cost-term error acquires the integer coefficient's size. -/
theorem gradient_cost_error {m c r r' δ : ℝ}
    (hm : 0≤m) (hr : 0<r) (hδ : 0≤δ) (he : |r'-1/r|≤δ/r) :
    |20*m*r'*c-20*m*r⁻¹*c|≤20*m*|c| *(δ/r) := by
  have heq : 20*m*r'*c-20*m*r⁻¹*c=(20*m*c)*(r'-1/r) := by rw [one_div]; ring
  rw [heq,abs_mul]
  have hc : |20*m*c|=20*m*|c| := by rw [abs_mul,abs_of_nonneg (by positivity : 0≤20*m)]
  rw [hc]
  exact mul_le_mul_of_nonneg_left he (by positivity)

/-- The error tolerance for the reciprocal term includes the slack range
three times: once for the reciprocal and twice for the smallest power. -/
theorem reciprocal_gradient_budget {r l : ℝ} {E K q : ℕ}
    (hr : 1/(2:ℝ)^E≤r) (hl : 1/(2:ℝ)^(2*E)≤l) :
    20*(2:ℝ)^K*((1/(2:ℝ)^(q+3*E+K+8))/r)≤((1/(2:ℝ)^q)/4)*l := by
  have hrpos : 0<r := lt_of_lt_of_le (by positivity) hr
  have hinv : 1/r≤(2:ℝ)^E := by
    apply (div_le_iff₀ hrpos).mpr
    have ht := mul_le_mul_of_nonneg_right hr (show (0:ℝ)≤(2:ℝ)^E by positivity)
    have he : (1/(2:ℝ)^E)*(2:ℝ)^E=1 := div_mul_cancel₀ 1 (by positivity)
    rw [he] at ht
    simpa only [mul_comm] using ht
  have hred : 20*(2:ℝ)^K*((1/(2:ℝ)^(q+3*E+K+8))/r)≤
      20*(2:ℝ)^K*(1/(2:ℝ)^(q+3*E+K+8))*(2:ℝ)^E := by
    rw [div_eq_mul_inv,← one_div r]
    have ht := mul_le_mul_of_nonneg_left hinv
      (show (0:ℝ)≤20*(2:ℝ)^K*(1/(2:ℝ)^(q+3*E+K+8)) by positivity)
    simpa only [mul_assoc] using ht
  have heq : 20*(2:ℝ)^K*(1/(2:ℝ)^(q+3*E+K+8))*(2:ℝ)^E=
      (20/256)*((1/(2:ℝ)^q)/(2:ℝ)^(2*E)) := by
    have he : q+3*E+K+8=q+2*E+K+E+8 := by omega
    rw [he]
    simp only [pow_add]
    norm_num
    field_simp
    <;> ring
  have hsmall : (20/256:ℝ)*((1/(2:ℝ)^q)/(2:ℝ)^(2*E))≤
      ((1/(2:ℝ)^q)/4)*(1/(2:ℝ)^(2*E)) := by
    have hn : 0≤(1/(2:ℝ)^q)/(2:ℝ)^(2*E) := by positivity
    have he : ((1/(2:ℝ)^q)/4)*(1/(2:ℝ)^(2*E))=
        (1/4)*((1/(2:ℝ)^q)/(2:ℝ)^(2*E)) := by ring
    rw [he]
    linarith only [hn]
  exact hred.trans (heq ▸ hsmall.trans
    (mul_le_mul_of_nonneg_left hl (by positivity)))

/-- The scalar formula for a stored edge gradient is the IPM formula once
the residual is decoded as `I.cost f-F`. -/
theorem gradient_from_slacks (I : Instance) (a F : ℝ) (f : Fin I.m→ℝ) (e : Fin I.m)
    {r g ε : ℝ} (hr : r=I.cost f-F)
    (he : |g-(20*(I.m:ℝ)*r⁻¹*((I.edge e).cost:ℝ)+
      a*Real.rpow (((I.edge e).upper:ℝ)-f e) (-1-a)-
      a*Real.rpow (f e-((I.edge e).lower:ℝ)) (-1-a))|≤
        ε*MinCostFlow.IPM.lengths I a f e) :
    |g-MinCostFlow.IPM.gradient I a F f e|≤ε*MinCostFlow.IPM.lengths I a f e := by
  subst r
  exact he

end MinCostFlow.Num.IPM
