module

public import MinCostFlow.Scaling.CanonicalSolver
public import MinCostFlow.Scaling.ApproximationModel
public import MinCostFlow.Scaling.ResidualBounds
import MinCostFlow.Scaling.ApproximationCorrectness
import MinCostFlow.Scaling.ObjectiveScanFacts
import Mathlib.Tactic.Ring

/-!
# Coordinate and magnitude bounds for capacity-scaling execution

Feasible integral flows use unsigned coordinates bounded by capacities.
The bottleneck candidate has that same feasibility property, so its
objective magnitude is at most `m*C*U`. A feasible residual correction
also preserves the original capacity constraints after augmentation.
These facts supply the arithmetic premises of the machine procedures.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Integer capacity constraints cast to the real constraints used by the
circulation lemmas. -/
theorem integral_capacity_bounds_cast (J : Circulation) (flow : Fin J.m → ℤ)
    (hf : ∀ e,0≤flow e ∧ flow e≤J.capacity e) :
    ∀ e,0≤(flow e : ℝ) ∧ (flow e : ℝ)≤J.capacity e := by
  intro e
  exact ⟨Int.cast_nonneg_iff.mpr (hf e).1,
    by simpa only [Int.cast_natCast] using (Int.cast_le (R := ℝ)).mpr (hf e).2⟩

/-- Feasible integral coordinates have fitting unsigned values under any
common capacity bound. -/
theorem feasible_unsigned_bounds (J : Circulation) (flow : Fin J.m → ℤ) (U : ℕ)
    (hf : J.Feasible (fun e => (flow e : ℝ))) (hu : ∀ e,J.capacity e≤U) :
    ∀ e,0≤flow e ∧ (flow e).toNat≤U := by
  intro e
  have hlo : 0≤flow e := Int.cast_nonneg_iff.mp (hf.2 e).1
  have hhi : flow e≤(J.capacity e : ℤ) :=
    Int.cast_le.mp (by simpa only [Int.cast_natCast] using (hf.2 e).2)
  have hnat : (flow e).toNat≤J.capacity e := by simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hhi
  exact ⟨hlo,hnat.trans (hu e)⟩

private theorem neg_toNat_le_natAbs (z : ℤ) : (-z).toNat≤z.natAbs := by
  cases z <;> simp

/-- The actual canonical approximation magnitude is bounded by the
capacity times cost budget summed over all edge slots. -/
theorem polyApprox_magnitude_le (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hC : J.CostsBounded C) (hu : ∀ e,J.capacity e≤U) :
    (polyApproxModel (canonicalSolver solver entry T hproc) J).value.magnitude≤J.m*(C*U) := by
  let solve := canonicalSolver solver entry T hproc
  let F := (polyApproxModel solve J).value.flow
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => canonicalSolver_optimal solver entry T hproc K
  have hfeas := (lemma_C_10 solve hsolve J hc).1
  have hvalues := feasible_unsigned_bounds J F U hfeas hu
  have hcast : (fun e => ((F e).toNat : ℤ))=F := by
    funext e
    exact Int.toNat_of_nonneg (hvalues e).1
  have hmass := objectiveScanMass_le J (fun e => (F e).toNat) (List.finRange J.m) C U
    (fun e _ => hC e) (fun e _ => (hvalues e).2)
  have habs := objectiveScan_natAbs_le J (fun e => (F e).toNat) (List.finRange J.m)
  rw [objectiveScan_finRange,hcast] at habs
  rw [List.length_finRange] at hmass
  rw [polyApproxModel_magnitude]
  exact (neg_toNat_le_natAbs (J.integerObjective F)).trans (habs.trans hmass)

/-- Any feasible integral residual correction gives a nonnegative
augmented flow within the original capacities, even without conservation
of the starting flow. -/
theorem residualAugment_integral_bounds (J : Circulation) (flow : Fin J.m → ℤ)
    (delta : Fin (J.m+J.m) → ℤ) (hf : ∀ e,0≤flow e ∧ flow e≤J.capacity e)
    (hd : (J.residual flow).Feasible (fun e => (delta e : ℝ))) :
    ∀ e,0≤flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) ∧
      flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e)≤J.capacity e := by
  have hreal := integral_capacity_bounds_cast J flow hf
  intro e
  have h := J.augment_bounds flow hreal (fun e => (delta e : ℝ)) hd e
  have heq : ((flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) : ℤ) : ℝ)=
      J.augment flow (fun e => (delta e : ℝ)) e := by
    simp only [Int.cast_add,Int.cast_sub,Circulation.augment,Circulation.project]
    ring
  have hlo : 0≤((flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) : ℤ) : ℝ) := by rw [heq]; exact h.1
  have hhi : ((flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) : ℤ) : ℝ)≤
      ((J.capacity e : ℤ) : ℝ) := by rw [Int.cast_natCast,heq]; exact h.2
  exact ⟨Int.cast_nonneg_iff.mp hlo,Int.cast_le.mp hhi⟩

end MinCostFlow.Scaling.Machine
