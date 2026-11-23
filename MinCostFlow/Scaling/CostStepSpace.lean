module

public import MinCostFlow.Scaling.CostStepContract
import MinCostFlow.Scaling.RoutedCapacitySpaceBounds

/-!
# A uniform polynomial reserve for one cost round

Include the rounded polynomial cost bound in a common numerical base.
That base bounds both actual inner capacity calls' dimensions and supplied
bounds. The primal call uses power 260, the dual call power 522, and all
remaining arrays use at most a cubic term. Power 524 covers their sum for
every current state, independently of its potentials or selected optimum.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Dimensions, rounding scale, and original cost and capacity bounds. -/
def costStepNumberBase (J : Circulation) (C U : ℕ) : ℕ :=
  J.n+4*J.m+(J.m+J.m)^10+C+U+8

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- Every state uses the same full cost-round workspace bound, including
both exact capacity-backed model calls and the final state arrays. -/
theorem costStepSpace_le (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    {J : Circulation} (s : CostState J) (C U : ℕ) :
    costStepSpace solver entry T hproc s C U≤(costStepNumberBase J C U)^524 := by
  let D := costStepNumberBase J C U
  let B := J.m+J.m
  let K := s.roundedInstance C
  let delta := (K.invokePositive (fun L => capacityScalingModel (canonicalSolver solver entry T hproc) L U)).value
  have hD : J.n+4*J.m+B^10+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hDpos : 0<D := by omega
  have hbase : capacityGraphSpaceBase K (B^10) U≤D := by
    change J.n+2*B+B^10+U+8≤D
    dsimp only [B] at hD ⊢
    omega
  have hP : capacityPositiveSpace K (B^10) U≤D^260 :=
    (capacityPositiveSpace_le K (B^10) U).trans (Nat.pow_le_pow_left hbase 260)
  have hQ : capacityExtractDualSpace K delta (B^10) U≤D^522 :=
    (capacityExtractDualSpace_le K delta (B^10) U).trans (Nat.pow_le_pow_left hbase 522)
  have h260_522 : D^260≤D^522 := Nat.pow_le_pow_right hDpos (by decide)
  have h64 : 64≤D^2 := Nat.pow_le_pow_left hD8 2
  have hlin : 9+45*J.m+2*J.n≤D^3 := by
    have h : 9+45*J.m+2*J.n≤12*D := by omega
    exact h.trans ((Nat.mul_le_mul_right D (show 12≤D^2 by omega)).trans_eq (pow_succ D 2).symm)
  have h3_522 : D^3≤D^522 := Nat.pow_le_pow_right hDpos (by decide)
  have hlast : 3*D^522≤D^523 :=
    (Nat.mul_le_mul_right (D^522) (show 3≤D by omega)).trans_eq (pow_succ' D 522).symm
  have h523_524 : D^523≤D^524 := Nat.pow_le_pow_right hDpos (by decide)
  change 2+10*J.m+(4+17*B)+capacityPositiveSpace K (B^10) U+
    capacityExtractDualSpace K delta (B^10) U+J.m+2*J.n+3≤D^524
  have hB : B=J.m+J.m := rfl
  omega

end MinCostFlow.Scaling.Machine
