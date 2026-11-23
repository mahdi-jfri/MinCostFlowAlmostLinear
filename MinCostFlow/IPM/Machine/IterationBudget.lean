module

public import MinCostFlow.IPM.Machine.RoundedIterationBound
import MinCostFlow.Num.IPM.AlphaFacts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# An integer iteration budget for the target-test program

The analytic count uses a real logarithm. The machine instead uses the
sum of binary input lengths and a power of two. For dyadic quality and
stored alpha, the requested step parameter is `2^(-(k+j+5))`. Its inverse
square is exactly the power used here, and binary input lengths bound
the logarithm from above. Thus the machine budget covers the analytic
count without a real-logarithm operation.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Integer arithmetic for a target test with `bits` bounding `log(mU)`
and dyadic quality and alpha exponents `k` and `j`. -/
def dyadicIterationBudget (m bits k j : ℕ) : ℕ :=
  800000*m*bits*2^(2*(k+j+5))

/-- The dyadic step parameter is exactly the product of the stored quality
and alpha divided by 32. -/
theorem dyadic_step_parameter (k j : ℕ) :
    1/(2:ℝ)^(k+j+5)=((1/(2:ℝ)^k)*(1/(2:ℝ)^j))/32 := by
  rw [pow_add,pow_add]
  norm_num
  ring

/-- The integer budget exactly cancels the requested parameter's square. -/
theorem dyadicIterationBudget_scaled (m bits k j : ℕ) :
    (dyadicIterationBudget m bits k j:ℝ)*(1/(2:ℝ)^(k+j+5))^2=
      800000*(m:ℝ)*bits := by
  simp only [dyadicIterationBudget,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  rw [show 2*(k+j+5)=(k+j+5)*2 by omega,pow_mul]
  field_simp

/-- The executable integer budget covers the scalar-rounded iteration
limit whenever `mU` is at least two. -/
theorem roundedIterationLimit_le_dyadicBudget (I : Instance) (U k j : ℕ)
    (hsize : 2≤I.m*U) :
    roundedIterationLimit I U (1/(2:ℝ)^(k+j+5))≤
      dyadicIterationBudget I.m (I.m.size+U.size) k j := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : (0:ℝ)<1/2^(k+j+5)))).mpr
  rw [dyadicIterationBudget_scaled]
  have hlog := (Num.IPM.alpha_bit_length_bounds hsize).1
  simp only [Nat.cast_mul] at hlog
  exact mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ)≤800000*I.m)

end MinCostFlow.IPM.Machine
