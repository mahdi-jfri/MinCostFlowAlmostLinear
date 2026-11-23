module

public import MinCostFlow.IPM.HiddenBounds
public import MinCostFlow.Basic.Hidden
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The parameters of the hidden stable instance

Theorem 4.6 (page 15) of arXiv:2309.16629v1 specifies a hidden stability
parameter of order `1/log m`, while the underlying barrier exponent is
`1/(1000 log(mU))`. Scaling every gradient by `log(mU)/log(m+2)`
normalizes the hidden ratio without changing circulations, lengths,
widths, or their stability. The Update normalization is scaled by the
same factor when this transformation is used by an IPM loop.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Multiply the gradients of a dynamic instance by a fixed scalar. -/
def scaleInstanceGradient (D : DynamicInstance) (s : ℝ) : DynamicInstance :=
  { D with g := fun t e => s*D.g t e }

/-- Positive gradient scaling changes only the hidden ratio parameter.
All five conditions of Definition 4.4 are preserved. -/
theorem hiddenStable_scaleGradient (D : DynamicInstance) (T : ℕ) (a Ψ s : ℝ)
    (hs : 0 ≤ s) (h : D.HiddenStable T a Ψ) :
    (scaleInstanceGradient D s).HiddenStable T (s*a) Ψ := by
  obtain ⟨c, w, hcw⟩ := h
  refine ⟨c, w, ?_⟩
  intro t ht
  have hh := hcw t ht
  refine ⟨hh.1, hh.2.1, ?_, hh.2.2.2.1, hh.2.2.2.2⟩
  change (D.G t).inner (fun e => s*D.g t e) (c t) / (D.G t).norm1 (w t) ≤ -(s*a)
  have hid : (D.G t).inner (fun e => s*D.g t e) (c t) = s*(D.G t).inner (D.g t) (c t) := by
    simp only [MGraph.inner, Finset.mul_sum, mul_assoc]
  rw [hid, mul_div_assoc]
  simpa only [mul_neg] using mul_le_mul_of_nonneg_left hh.2.2.1 hs

/-- A fully explicit version of the `1/Θ(log m)` parameter of Theorem 4.6.
Using `m+2` includes graphs with one edge. -/
def normalizedIpmAlpha (I : Instance) : ℝ := 1/(8000*Real.log (I.m+2))

/-- Padding the edge count makes the normalized hidden parameter
positive even for the small graph cases. -/
theorem normalizedIpmAlpha_pos (I : Instance) : 0 < normalizedIpmAlpha I := by
  have hm : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
  unfold normalizedIpmAlpha
  exact one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos (by linarith only [hm])))

/-- Explicit constants for the `1/Θ(log m)` parameter in Theorem 4.6
(page 15): for at least two edges, the normalized parameter lies
between `1/(16000 log m)` and `1/(8000 log m)`. The padded definition
also remains positive on the one-edge case. -/
theorem normalizedIpmAlpha_bounds (I : Instance) (hm : 2 ≤ I.m) :
    1/(16000*Real.log I.m) ≤ normalizedIpmAlpha I ∧
      normalizedIpmAlpha I ≤ 1/(8000*Real.log I.m) := by
  have hmR : (2 : ℝ) ≤ I.m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < I.m := lt_of_lt_of_le (by norm_num) hmR
  have hlogpos : 0 < Real.log I.m := Real.log_pos (lt_of_lt_of_le (by norm_num) hmR)
  have hlo : Real.log I.m ≤ Real.log (I.m+2) :=
    Real.log_le_log hmpos (by linarith only [hmR])
  have hpoly : (I.m : ℝ)+2 ≤ (I.m : ℝ)^2 := by nlinarith only [hmR]
  have hhi := Real.log_le_log (by linarith only [hmR] : (0 : ℝ) < I.m+2) hpoly
  rw [Real.log_pow] at hhi
  norm_num only [Nat.cast_ofNat] at hhi
  have hpad : 0 < Real.log (I.m+2) := hlogpos.trans_le hlo
  unfold normalizedIpmAlpha
  constructor
  · apply (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16000) hlogpos)
      (mul_pos (by norm_num : (0 : ℝ) < 8000) hpad)).mpr
    linarith only [hhi]
  · apply (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8000) hpad)
      (mul_pos (by norm_num : (0 : ℝ) < 8000) hlogpos)).mpr
    linarith only [hlo]

/-- The gradient scale that converts the barrier witness ratio `α/8`
into `normalizedIpmAlpha`, without changing the chosen flow direction. -/
def ipmGradientScale (I : Instance) (U : ℝ) : ℝ :=
  Real.log (I.m*U)/Real.log (I.m+2)

/-- The fixed gradient normalization is positive in the IPM range. -/
theorem ipmGradientScale_pos (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    0 < ipmGradientScale I U := by
  have hm2 : (1 : ℝ) < I.m+2 := by
    have hm0 : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
    linarith only [hm0]
  exact div_pos (lt_of_lt_of_le (by norm_num) (log_size_ge_half I U hsize))
    (Real.log_pos hm2)

/-- Exact relation between the barrier witness ratio and the normalized
hidden parameter used by the data structure. -/
theorem ipmGradientScale_mul_alpha (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    ipmGradientScale I U*(alpha I U/8) = normalizedIpmAlpha I := by
  have hm2 : (1 : ℝ) < I.m+2 := by
    have hm0 : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
    linarith only [hm0]
  have hmLog := Real.log_pos hm2
  have hxLog : 0 < Real.log (I.m*U) := lt_of_lt_of_le (by norm_num) (log_size_ge_half I U hsize)
  unfold ipmGradientScale alpha normalizedIpmAlpha
  field_simp [hxLog.ne', hmLog.ne']
  norm_num

/-- The normalized hidden parameter follows by scaling gradients; it is
not obtained by identifying `log(mU)` with `log m` for large capacities. -/
theorem hiddenStable_normalized (I : Instance) (U : ℝ) (D : DynamicInstance) (T : ℕ)
    (hsize : 2 ≤ (I.m : ℝ)*U)
    (h : D.HiddenStable T (alpha I U/8) (ipmPsi I U)) :
    (scaleInstanceGradient D (ipmGradientScale I U)).HiddenStable T
      (normalizedIpmAlpha I) (ipmPsi I U) := by
  have hm2 : (1 : ℝ) < I.m+2 := by
    have hm0 : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
    linarith only [hm0]
  have hmLog := Real.log_pos hm2
  have hxLog : 0 < Real.log (I.m*U) := lt_of_lt_of_le (by norm_num) (log_size_ge_half I U hsize)
  have hs : 0 ≤ ipmGradientScale I U := div_nonneg hxLog.le hmLog.le
  have hh := hiddenStable_scaleGradient D T (alpha I U/8) (ipmPsi I U)
    (ipmGradientScale I U) hs h
  have heq : ipmGradientScale I U*(alpha I U/8) = normalizedIpmAlpha I := by
    unfold ipmGradientScale alpha normalizedIpmAlpha
    field_simp [hxLog.ne', hmLog.ne']
    norm_num
  simpa only [heq] using hh

/-- The explicit item-5 parameter is bounded by `23000 log²(mU)`.
Thus quasipolynomial costs and capacities give the logarithmic magnitude
bound required by Definition 4.4. -/
theorem ipmPsi_le (I : Instance) (U : ℝ) (hm : 0 < I.m) (hU : 1 ≤ U)
    (hsize : 2 ≤ (I.m : ℝ)*U) : ipmPsi I U ≤ 23000*(Real.log (I.m*U))^2 := by
  have hmR : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hm0 : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hx0 : 0 < (I.m : ℝ)*U := mul_pos hm0 hU0
  have hxlog := log_size_ge_half I U hsize
  have hxlog0 : 0 < Real.log (I.m*U) := lt_of_lt_of_le (by norm_num) hxlog
  have hlogm : Real.log I.m ≤ Real.log (I.m*U) := Real.log_le_log hm0 (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hU hm0.le)
  have hlogU : Real.log U ≤ Real.log (I.m*U) := Real.log_le_log hU0 (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hmR hU0.le)
  have hlog2 : Real.log 2 ≤ Real.log (I.m*U) := Real.log_le_log (by norm_num) hsize
  have hlog400 : Real.log 400 ≤ 9*Real.log (I.m*U) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 400)
      (by norm_num : (400 : ℝ) ≤ 2^9)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, hlog2]
  have hlog100 : Real.log 100 ≤ 7*Real.log (I.m*U) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ 2^7)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, hlog2]
  have hloglog : Real.log (Real.log (I.m*U)) ≤ Real.log (I.m*U) :=
    Real.log_le_log hxlog0 (Real.log_le_self hx0.le)
  have hlogB : Real.log (ipmBarrierBound I U) ≤ 11*Real.log (I.m*U) := by
    unfold ipmBarrierBound
    rw [Real.log_mul (mul_ne_zero (by norm_num) hm0.ne') hxlog0.ne',
      Real.log_mul (by norm_num : (400 : ℝ) ≠ 0) hm0.ne']
    linarith only [hlog400, hlogm, hloglog]
  have hlogB0 := Real.log_nonneg (ipmBarrierBound_ge_one I U hm hsize)
  have ha := alpha_pos I U hsize
  have ha1 : alpha I U ≤ 1 := (alpha_le I U hsize).trans (by norm_num)
  have hfactor : (1+alpha I U)/alpha I U ≤ 2/alpha I U := by
    apply (div_le_div_iff_of_pos_right ha).mpr
    linarith only [ha1]
  have hQ : ipmLogScale I U ≤ 22000*(Real.log (I.m*U))^2 := by
    calc
      _ ≤ (2/alpha I U)*(11*Real.log (I.m*U)) :=
        mul_le_mul hfactor hlogB hlogB0 (div_nonneg (by norm_num) ha.le)
      _ = _ := by unfold alpha; simp only [div_eq_mul_inv, one_mul, inv_inv]; ring
  have h2U : Real.log (2*U) ≤ 2*Real.log (I.m*U) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hU0.ne']
    linarith only [hlog2, hlogU]
  have hpay : 11*Real.log (I.m*U) ≤ 22*(Real.log (I.m*U))^2 := by
    nlinarith only [hxlog]
  unfold ipmPsi
  nlinarith only [hlog100, hQ, h2U, hpay, sq_nonneg (Real.log (I.m*U))]

end MinCostFlow.IPM
