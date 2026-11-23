module

public import MinCostFlow.Scaling.CostCapacityContract
import MinCostFlow.Scaling.CostCapacityCorrectness

/-!
# Bounds on the exact composed circulation output

The proved optimality of the actual cost-capacity model implies that each
returned integral coordinate lies between zero and its input capacity.
These bounds justify conversion to unsigned magnitudes and then back to
the canonical signed pairs used by the general-flow reduction.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The actual composed model returns nonnegative integral coordinates
bounded by the supplied capacity budget. -/
theorem costCapacityModel_output_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    ∀ e,0≤(costCapacityModel (canonicalSolver solver entry T hproc) J C U).value e ∧
      ((costCapacityModel (canonicalSolver solver entry T hproc) J C U).value e).natAbs≤U := by
  have hopt := costCapacityModel_optimal (canonicalSolver solver entry T hproc)
    (fun K _ _ => canonicalSolver_optimal solver entry T hproc K) J C U hU hC hu
  intro e
  have hlo : 0≤(costCapacityModel (canonicalSolver solver entry T hproc) J C U).value e :=
    Int.cast_nonneg_iff.mp (hopt.1.2 e).1
  have hhi : (costCapacityModel (canonicalSolver solver entry T hproc) J C U).value e≤(U : ℤ) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using ((hopt.1.2 e).2.trans (by exact_mod_cast hu e))
  have habs := congrArg Int.natAbs (Int.toNat_of_nonneg hlo)
  simp only [Int.natAbs_natCast] at habs
  refine ⟨hlo,?_⟩
  rw [←habs]
  simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hhi

end MinCostFlow.Scaling.Machine
