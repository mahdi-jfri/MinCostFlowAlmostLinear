module

public import MinCostFlow.Scaling.BottleneckTestProgram
import WordRAM.LinkDefs

/-!
# Uniform budgets for a finite bottleneck search

The binary search tests only stored candidate thresholds. The maximum of
their canonical guest widths bounds every test's fresh region and setup
cost. Solver dimensions stay fixed throughout the search.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Maximum canonical guest width among the stored threshold candidates. -/
def bottleneckGuestBound (J : Circulation) (candidates : List ℕ) : ℕ :=
  (candidates.map (fun u => wordSize 5 (J.bottleneckGraph u).positiveInstance.solverWords)).foldr max 0

/-- Every candidate's guest width is at most the common search bound. -/
theorem bottleneckGuest_le (J : Circulation) {candidates : List ℕ} {u : ℕ}
    (hu : u ∈ candidates) :
    wordSize 5 (J.bottleneckGraph u).positiveInstance.solverWords ≤ bottleneckGuestBound J candidates :=
  Link.elem_le_foldr_max (List.mem_map.mpr ⟨u,hu,rfl⟩)

/-- One test's complete fresh allocation is bounded uniformly over the
candidate list. Five further words suffice for its new search header. -/
theorem bottleneckTest_space_le (J : Circulation) {candidates : List ℕ} {u : ℕ}
    (hu : u ∈ candidates) :
    7+15*J.m+2^(wordSize 5 (J.bottleneckGraph u).positiveInstance.solverWords)+5 ≤
      12+15*J.m+2^(bottleneckGuestBound J candidates) := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (bottleneckGuest_le J hu)
  omega

/-- Uniform cost of a test, in the solver dimensions of the original
circulation, with only linear edge work and the canonical width overhead. -/
theorem bottleneckTest_cost_le (w : ℕ) (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) {candidates : List ℕ} {u : ℕ} (hu : u ∈ candidates)
    (C : ℕ) (args : List ℕ) (mem : ℕ → ℕ) :
    (bottleneckTestContract w solver f T hproc J u C).cost args mem ≤
      (solver.regBound+6)*T (J.n+1) J.m+40*bottleneckGuestBound J candidates+
        solver.regBound+1500*J.m+1760 := by
  have hwidth := bottleneckGuest_le J hu
  change (solver.regBound+6)*T (J.n+1) J.m+
    80*(J.bottleneckGraph u).positiveInstance.solverWords.length+
      40*wordSize 5 (J.bottleneckGraph u).positiveInstance.solverWords+solver.regBound+1100*J.m+1600 ≤ _
  rw [Circulation.solverWords_length]
  change (solver.regBound+6)*T (J.n+1) J.m+
    80*(2+5*J.m)+40*wordSize 5 (J.bottleneckGraph u).positiveInstance.solverWords+
      solver.regBound+1100*J.m+1600 ≤ _
  omega

end MinCostFlow.Scaling.Machine
