module

public import MinCostFlow.Scaling.ZeroCapacitySolveProgram
public import MinCostFlow.Scaling.BottleneckSearch
public import MinCostFlow.Scaling.ObjectiveScanFacts

/-!
# Arithmetic bounds for bottleneck threshold solves

A threshold graph has capacities zero or one. Its exact integral optimum
therefore has unsigned coordinates at most one. The objective scan needs
at most `m*C` magnitude budget when costs have magnitude at most `C`.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every threshold query meets the capacity bound of the exact solver
adapter, including graphs with no edge slots. -/
theorem bottleneckGraph_capacity_bound (J : Circulation) (B : ℕ) :
    ∀ e,(J.bottleneckGraph B).capacity e ≤ (J.bottleneckGraph B).m^40 := by
  intro e
  have hm : 0<J.m := Nat.zero_lt_of_lt e.isLt
  exact (J.bottleneckGraph_capacities B e).trans (Nat.pow_pos hm)

/-- Thresholding preserves the original costs and hence every cost bound. -/
theorem bottleneckGraph_costsBounded (J : Circulation) (B C : ℕ)
    (hc : J.CostsBounded C) : (J.bottleneckGraph B).CostsBounded C := hc

/-- Every threshold-graph word fits whenever the original graph words and
one fit. The new capacities are only zero and one. -/
theorem bottleneckGraph_words_fit (J : Circulation) (B w : ℕ)
    (hinput : ∀ x ∈ J.solverWords,x<2^w) (hw : 1<2^w) :
    ∀ x ∈ (J.bottleneckGraph B).solverWords,x<2^w := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hinput _ List.mem_cons_self
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨e,_,hx⟩ := List.mem_flatMap.mp hx
  change x ∈ [(J.tail e).val,(J.head e).val,(J.bottleneckGraph B).capacity e,
    if J.cost e<0 then 1 else 0,(J.cost e).natAbs] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  · exact (J.bottleneckGraph_capacities B e).trans_lt hw
  · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))

/-- Optimality of the actual canonical solve supplies unit unsigned
coordinates. No choice of optimum is imposed on the solver. -/
theorem bottleneckSolve_toNat_le_one (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (B : ℕ) :
    ∀ e,(Circulation.solveWithZeroCapacities (canonicalSolver solver f T hproc)
      (J.bottleneckGraph B) e).toNat ≤ 1 := by
  let K := J.bottleneckGraph B
  let delta := Circulation.solveWithZeroCapacities (canonicalSolver solver f T hproc) K
  have hopt : K.Optimal (fun e => (delta e : ℝ)) := by
    apply Circulation.solveWithZeroCapacities_of_optimal
    exact canonicalSolver_optimal solver f T hproc K.positiveInstance
  intro e
  have hb : delta e ≤ (K.capacity e : ℤ) :=
    Int.cast_le.mp (by simpa only [Int.cast_natCast] using (hopt.1.2 e).2)
  have hn : (delta e).toNat ≤ K.capacity e := by
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hb
  exact hn.trans (J.bottleneckGraph_capacities B e)

/-- A unit-capacity solve's full objective budget is bounded by `m*C`. -/
theorem bottleneckSolve_objective_mass_le (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (B C : ℕ) (hc : J.CostsBounded C) :
    objectiveScanMass (J.bottleneckGraph B)
      (fun e => (Circulation.solveWithZeroCapacities (canonicalSolver solver f T hproc)
        (J.bottleneckGraph B) e).toNat) (List.finRange J.m) ≤ J.m*C := by
  have h := objectiveScanMass_le (J.bottleneckGraph B)
    (fun e => (Circulation.solveWithZeroCapacities (canonicalSolver solver f T hproc)
      (J.bottleneckGraph B) e).toNat) (List.finRange J.m) C 1
    (fun e _ => hc e) (fun e _ => bottleneckSolve_toNat_le_one solver f T hproc J B e)
  simpa only [List.length_finRange,Nat.mul_one] using h

end MinCostFlow.Scaling.Machine
