module

public import MinCostFlow.Scaling.BottleneckSolveBounds
import MinCostFlow.Scaling.BottleneckSelection

/-!
# Bounds for the exact retained bottleneck result

The proved selection invariant identifies the retained flow with the
actual unit-capacity solve at a sorted capacity slot. Thus its coordinates
are nonnegative and at most one. Its threshold is an original capacity
and is bounded by any bound on the original capacities.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A retained result has bounded threshold and nonnegative unit flow,
using only the actual canonical solver's established optimality. -/
theorem bottleneckSearch_best_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hu : ∀ e,J.capacity e≤U) (u : ℕ) (flow : Fin J.m → ℤ)
    (hbest : (bottleneckSearch (canonicalSolver solver entry T hproc) J).value.best=some (u,flow)) :
    u≤U ∧ ∀ e,0≤flow e ∧ (flow e).toNat≤1 := by
  let solve := canonicalSolver solver entry T hproc
  let candidates := (sortCapacities (List.ofFn J.capacity)).1
  let s := (bottleneckSearch solve J).value
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => canonicalSolver_optimal solver entry T hproc K
  have hselection := bottleneckSearch_selection solve hsolve J hc
  have hb := hselection.2.2.2
  change (match s.best with | none => _ | some (u,flow) => _) at hb
  rw [hbest] at hb
  have hindex : s.lower-1<candidates.length := by
    have hsame : s.lower=s.upper := hselection.1
    have hend : s.upper≤candidates.length := hselection.2.1
    have hpos : 0<s.lower := hb.1
    omega
  have hmem : u∈candidates := by
    rw [hb.2.1]
    change candidates.getD (s.lower-1) 0∈candidates
    simpa only [List.getD,List.getElem?_eq_getElem hindex,Option.getD_some] using List.getElem_mem hindex
  have hcapacity : ∃ e : Fin J.m,J.capacity e=u :=
    List.mem_ofFn.mp ((sortCapacities_perm _).mem_iff.mp hmem)
  refine ⟨?_,?_⟩
  · obtain ⟨e,he⟩ := hcapacity
    rw [←he]
    exact hu e
  · have hopt := J.bottleneckTest_optimal solve hsolve hc u
    rw [←hb.2.2.1] at hopt
    intro e
    have hlo : 0≤flow e := Int.cast_le.mp (by simpa only [Int.cast_zero] using (hopt.1.2 e).1)
    have hhi : flow e≤((J.bottleneckGraph u).capacity e : ℤ) :=
      Int.cast_le.mp (by simpa only [Int.cast_natCast] using (hopt.1.2 e).2)
    refine ⟨hlo,?_⟩
    have hnat := Int.toNat_le_toNat hhi
    simp only [Int.toNat_natCast] at hnat
    exact hnat.trans (J.bottleneckGraph_capacities u e)

end MinCostFlow.Scaling.Machine
