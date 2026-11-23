module

public import MinCostFlow.IPM.Machine.SolverPenalty
public import MinCostFlow.IPM.Machine.InitialFlow
public import MinCostFlow.IPM.Machine.PrecisionProducts
import MinCostFlow.IPM.InitialSize
import MinCostFlow.IPM.InitialDomain
import MinCostFlow.IPM.Machine.InitialPolynomialSize
import Mathlib.Tactic

/-!
# Bounded solver parameters for the augmented instance

The polynomial bounds in Lemma C.1 of Chen et al. (arXiv:2203.00671v2)
give the (U) used in Lemma 4.12 (page 31). The penalty bounds every
augmented coefficient and is itself polynomial in the original edge count.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Scaling

/-- Penalty used both on the machine and in the augmented instance. -/
def solverPenalty (m : ℕ) : ℕ := 4*m*(solverCapacityBound m)^2

/-- The instance built by calling Lemma 4.12 on the bounded input. -/
def solverAugmented (J : Circulation) : Instance :=
  initialInstance J.toInstance (solverPenalty J.m : ℤ)

/-- The bounded solver's capacity and cost hypotheses imply the shared
input bound used by the initialization. -/
theorem solverCapacityBound_input (J : Circulation) (hm : 0 < J.m)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e, J.capacity e ≤ J.m^40) :
    (∀ e, J.capacity e ≤ solverCapacityBound J.m) ∧ J.CostsBounded (solverCapacityBound J.m) := by
  exact ⟨fun e => (hu e).trans (le_max_right _ _),
    fun e => (hc e).trans ((Nat.pow_le_pow_right hm (by decide : 10 ≤ 40)).trans (le_max_right _ _))⟩

/-- The initialization uses at most (16m^{81}) for its penalty.
In particular, it increases bit lengths by only a constant factor. -/
theorem solverPenalty_le (m : ℕ) (hm : 0 < m) : solverPenalty m ≤ 16*m^81 := by
  have hpow : 1 ≤ m^40 := Nat.one_le_pow _ _ hm
  have hU : solverCapacityBound m ≤ 2*m^40 := by
    unfold solverCapacityBound
    exact max_le (by omega) (by omega)
  calc
    solverPenalty m ≤ 4*m*(2*m^40)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU 2)
    _ = 16*m^81 := by ring

/-- The augmented edge count lies between the original count and three
times that count. A zero-demand circulation has no nonzero imbalance
at an isolated vertex. -/
theorem solverAugmented_size (J : Circulation) (hu : ∀ e, 1 ≤ J.capacity e) :
    J.m ≤ (solverAugmented J).m ∧ (solverAugmented J).m ≤ 3*J.m := by
  constructor
  · exact circulation_augmented_m_ge J _ hu
  · have h := initialInstance_m_le J.toInstance (solverPenalty J.m : ℤ) (by
      intro v _
      simp [Instance.d])
    simpa only [solverAugmented,Circulation.toInstance_m] using h

/-- Appendix C's compressed vertex bound survives both the dummy-loop
vertex and the single additional vertex of the Lemma 4.12 augmentation. -/
theorem solverAugmented_vertices_le (J : Circulation) (hn : J.n ≤ 2*J.m+1)
    (hu : ∀ e, 1 ≤ J.capacity e) :
    (solverAugmented J).n ≤ 2*(solverAugmented J).m+2 := by
  change J.n+1 ≤ _
  have hm := (solverAugmented_size J hu).1
  omega

end MinCostFlow.IPM.Machine
