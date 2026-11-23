module

public import MinCostFlow.Scaling.CapacityResidualSpace
import MinCostFlow.Scaling.CapacityRoundedSpace

/-!
# One uniform capacity-step workspace reserve

Use the common numerical base as a dimensions-and-cost
bound for the residual rounded solve. Its reserve is at most power 218
of the base. The residual graph, approximation, and new state use smaller
powers. Power 256 bounds their sum uniformly over the current flow and
chosen approximation magnitude.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every capacity-bounded state fits the same polynomial fresh-space
reserve, independently of its stop flag and actual selected magnitude. -/
theorem capacityStepSpace_le (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (hm : 0<J.m)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) :
    capacityStepSpace solver entry T hproc J s≤(capacityStepNumberBase J C U)^256 := by
  let D := capacityStepNumberBase J C U
  let R := J.residual s.flow
  let B := (polyApproxModel (canonicalSolver solver entry T hproc) R).value.magnitude
  change capacityStepSpace solver entry T hproc J s≤D^256
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hDpos : 0<D := by omega
  have hfourD : 4*D≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul_right D hD4
  have h16 : 16≤D^2 := Nat.pow_le_pow_left hD4 2
  have hcost : R.CostsBounded D := by
    intro e
    have h := J.residual_costsBounded s.flow C hC e
    exact h.trans (by omega)
  have hQS : capacityRoundedSpace R B≤D^218 := capacityRoundedSpace_le R B D hD4
    (by change J.n≤D; omega) (by change J.m+J.m≤D; omega) hcost
    (by change 0<J.m+J.m; omega)
  have hAP : capacityApproxSpace R≤D^56 := capacityApproxSpace_le J s C U hf hC hu
  have h2_218 : D^2≤D^218 := Nat.pow_le_pow_right hDpos (by decide)
  have h56_218 : D^56≤D^218 := Nat.pow_le_pow_right hDpos (by decide)
  have h38 : 16≤D^38 := h16.trans (Nat.pow_le_pow_right hDpos (by decide : 2≤38))
  have h256 : 16*D^218≤D^256 := by
    have h := Nat.mul_le_mul_right (D^218) h38
    simpa only [←pow_add] using h
  have hlinear : 2+10*J.m+J.m+2+4≤3*D^2 := by omega
  change 2+10*J.m+capacityApproxSpace R+capacityRoundedSpace R B+J.m+2+4≤D^256
  omega

end MinCostFlow.Scaling.Machine
