module

public import MinCostFlow.Scaling.CapacityPositiveContract

/-!
# Uniform polynomial space for complete capacity-model calls

The source dimensions and supplied cost and capacity bounds control every
term in the complete capacity wrapper's reserve. An extra four units in
the numerical base also cover the positive adapter's added isolated
vertex. The logarithmic round count contributes only three powers of this
base, so power 260 covers the whole adapter and its final erased array.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A dimensions-and-bounds base including positive-adapter header margin. -/
def capacityGraphSpaceBase (J : Circulation) (C U : ℕ) : ℕ := J.n+2*J.m+C+U+8

set_option exponentiation.threshold 512 in
set_option maxRecDepth 2048 in
/-- Every positive capacity-model invocation has the same fixed polynomial
reserve bound, without assuming any property of a selected optimum. -/
theorem capacityPositiveSpace_le (J : Circulation) (C U : ℕ) :
    capacityPositiveSpace J C U≤(capacityGraphSpaceBase J C U)^260 := by
  let D := capacityGraphSpaceBase J C U
  let fuel := capacityRounds J.m U
  let N := (capacityStepNumberBase J.positiveInstance C U)^256
  have hD : J.n+2*J.m+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hDpos : 0<D := by omega
  have hbase : capacityStepNumberBase J.positiveInstance C U≤D := by
    change J.n+1+2*J.m+C+U+4≤D
    omega
  have hN : N≤D^256 := Nat.pow_le_pow_left hbase 256
  have hmLog : Nat.clog 2 (J.m+1)≤J.m+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have huLog : Nat.clog 2 (U+1)≤U+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hfuelLinear : fuel+1≤14*D := by
    change 1+11*Nat.clog 2 (J.m+1)+Nat.clog 2 (U+1)+1≤14*D
    omega
  have h64 : 64≤D^2 := Nat.pow_le_pow_left hD8 2
  have hD3 : 16*D≤D^3 := by
    simpa only [←pow_succ] using Nat.mul_le_mul (show 16≤D^2 by omega) (le_refl D)
  have hfuel : fuel+1≤D^3 := hfuelLinear.trans (by omega)
  have hcells : (fuel+1)*N≤D^259 := by
    simpa only [←pow_add] using Nat.mul_le_mul hfuel hN
  have hlinear : J.n+13*J.m+11≤D^2 := by
    have h : J.n+13*J.m+11≤7*D := by omega
    exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right D (show 7≤D by omega))
  have h2_259 : D^2≤D^259 := Nat.pow_le_pow_right hDpos (by decide)
  have hlast : 2*D^259≤D^260 := by
    exact (Nat.mul_le_mul_right (D^259) (show 2≤D by omega)).trans_eq (pow_succ' D 259).symm
  change 2+5*J.m+capacityScalingSpace J.positiveInstance C U+J.m+2≤D^260
  unfold capacityScalingSpace
  rw [J.positiveInstance.solverWords_length]
  change 2+5*J.m+(2+5*J.m+(J.n+1)+2+J.m+2+(fuel+1)*N+J.m)+J.m+2≤D^260
  omega

/-- The non-adapted capacity wrapper needs no more reserve than its
positive-adapter invocation on the same original dimensions and bounds. -/
theorem capacityScalingSpace_le_positiveSpace (J : Circulation) (C U : ℕ) :
    capacityScalingSpace J C U≤capacityPositiveSpace J C U := by
  have hp : (capacityStepNumberBase J C U)^256≤(capacityStepNumberBase J.positiveInstance C U)^256 := by
    apply Nat.pow_le_pow_left
    change J.n+2*J.m+C+U+4≤J.n+1+2*J.m+C+U+4
    omega
  have hmul := Nat.mul_le_mul_left (capacityRounds J.m U+1) hp
  unfold capacityPositiveSpace capacityScalingSpace
  rw [J.solverWords_length,J.positiveInstance.solverWords_length]
  change 2+5*J.m+J.n+2+J.m+2+(capacityRounds J.m U+1)*(capacityStepNumberBase J C U)^256+J.m≤
    2+5*J.m+(2+5*J.m+(J.n+1)+2+J.m+2+
      (capacityRounds J.m U+1)*(capacityStepNumberBase J.positiveInstance C U)^256+J.m)+J.m+2
  omega

/-- The complete capacity wrapper also fits the fixed power-260 reserve. -/
theorem capacityScalingSpace_le (J : Circulation) (C U : ℕ) :
    capacityScalingSpace J C U≤(capacityGraphSpaceBase J C U)^260 :=
  (capacityScalingSpace_le_positiveSpace J C U).trans (capacityPositiveSpace_le J C U)

end MinCostFlow.Scaling.Machine
