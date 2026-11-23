module

public import MinCostFlow.Num.FixedDivide
public import MinCostFlow.Num.ApproximationFacts
public import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Tactic

/-!
# Rounded division for the gradient cost term

The cost coefficient is an integer. Loading it at the shared precision
before division avoids multiplying a reciprocal error by that coefficient.
The only error is then one unit in the last place, which can be compared
with the dyadic lower bound on an edge length.
-/

public section
namespace MinCostFlow.Num.IPM

/-- Fixed-point division is real division rounded down at the shared scale. -/
theorem fixed_divide_floor {mem : ℕ→ℕ} {a d h L P : ℕ} :
    floorDiv (intVal mem a h L*(2:ℤ)^P) (intVal mem d h L)=
      ⌊(fixVal mem a h L P/fixVal mem d h L P)*(2:ℝ)^P⌋ := by
  rw [floorDiv_eq_floor]
  congr 1
  simp only [fixVal,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  field_simp

/-- Three guard bits cover a rounded signed quotient in the stated range. -/
theorem floor_scaled_fits {x : ℝ} {h L P D : ℕ}
    (hx : |x|≤(2:ℝ)^D) (hwidth : P+D+3≤h*L) :
    Fits h L ⌊x*(2:ℝ)^P⌋ := by
  have he := floor_scaled_error x P
  have hb : |(⌊x*(2:ℝ)^P⌋:ℝ)/(2:ℝ)^P|≤(2:ℝ)^(D+1) := by
    have ht : |(⌊x*(2:ℝ)^P⌋:ℝ)/(2:ℝ)^P|≤
        |(⌊x*(2:ℝ)^P⌋:ℝ)/(2:ℝ)^P-x|+|x| := by
      simpa only [sub_add_cancel] using
        abs_add_le ((⌊x*(2:ℝ)^P⌋:ℝ)/(2:ℝ)^P-x) x
    have hu : 1/(2:ℝ)^P≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
    have hD : (1:ℝ)≤(2:ℝ)^D := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith only [ht,he,hx,hu,hD]
  exact fits_of_scaled_bound (P:=P) (E:=D+1) (by omega) hb

/-- A bounded numerator divided by a dyadically bounded positive residual
has a dyadic quotient bound. -/
theorem quotient_bound {n r : ℝ} {K E : ℕ}
    (hn : |n|≤(2:ℝ)^K) (hr : 1/(2:ℝ)^E≤r) :
    |n/r|≤(2:ℝ)^(K+E) := by
  have hrpos : 0<r := lt_of_lt_of_le (by positivity) hr
  rw [abs_div,abs_of_pos hrpos]
  apply (div_le_iff₀ hrpos).mpr
  have ht := mul_le_mul_of_nonneg_right hr (show (0:ℝ)≤(2:ℝ)^E by positivity)
  rw [div_mul_cancel₀ 1 (by positivity)] at ht
  have ht' := mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤(2:ℝ)^K by positivity)
  rw [pow_add]
  nlinarith only [hn,ht']

/-- The real error of a fixed-division output is at most one output unit. -/
theorem fixedDivide_output_error {w h a d L P heap v : ℕ} {mem mem' : ℕ→ℕ}
    (hout : (fixedDivideContract w h).post [a,d,L,P,heap] mem v mem') :
    |fixVal mem' (v-L) h L P-fixVal mem a h L P/fixVal mem d h L P|≤1/(2:ℝ)^P := by
  have he := hout.2.2.2.2.2.2
  change intVal mem' (heap+9*L+integerDivideSpace (3*L)) h L=
    floorDiv (intVal mem a h L*(2:ℤ)^P) (intVal mem d h L) at he
  have hv := hout.1
  change v=heap+fixedDivideSpace L at hv
  have hp : v-L=heap+9*L+integerDivideSpace (3*L) := by
    rw [hv]; unfold fixedDivideSpace; omega
  rw [hp]
  simp only [fixVal,he]
  rw [fixed_divide_floor]
  exact floor_scaled_error _ _

/-- Output precision covering the smallest slack power makes each division
or product rounding cost at most one eighth of the gradient tolerance. -/
theorem unit_gradient_budget {l : ℝ} {E P q : ℕ}
    (hl : 1/(2:ℝ)^(2*E)≤l) (hprec : q+2*E+3≤P) :
    1/(2:ℝ)^P≤((1/(2:ℝ)^q)/8)*l := by
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hprec
  have he : 1/(2:ℝ)^(q+2*E+3)=((1/(2:ℝ)^q)/8)*(1/(2:ℝ)^(2*E)) := by
    simp only [pow_add]
    norm_num
    ring
  calc
    _ ≤ 1/(2:ℝ)^(q+2*E+3) := one_div_le_one_div_of_le (by positivity) hp
    _ = _ := he
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

end MinCostFlow.Num.IPM
