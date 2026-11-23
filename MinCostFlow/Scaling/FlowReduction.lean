module

public import MinCostFlow.Scaling.Circulation
public import MinCostFlow.Statement.Problem
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Removing lower capacities and demands

The proof of Lemma C.1 in Chen et al., arXiv:2203.00671v2, Appendix C,
reduces general minimum-cost flow to minimum-cost circulation. The source
leaves the reduction implicit. We first subtract the lower capacities.
This gives nonnegative capacities and subtracts the lower flow's balance
from each demand. The change of objective is a fixed additive constant.
-/

@[expose] public section
namespace MinCostFlow.Scaling

namespace FlowReduction

/-- The integer incidence coefficient of an edge of the input instance. -/
def coefficient (I : Instance) (e : Fin I.m) (v : Fin I.n) : ℤ :=
  (if v.val = (I.edge e).tail then 1 else 0) -
  (if v.val = (I.edge e).head then 1 else 0)

/-- Demands after subtracting the original lower-capacity vector. -/
def shiftedDemand (I : Instance) (v : Fin I.n) : ℤ :=
  I.d v - ∑ e, coefficient I e v * (I.edge e).lower

/-- The nonnegative-capacity graph after subtracting lower capacities.
The prescribed demands are `shiftedDemand`, rather than zero at this stage. -/
abbrev shiftedGraph (I : Instance) (hv : I.IsValid) : Circulation where
  n := I.n
  m := I.m
  tail := fun e => ⟨(I.edge e).tail, (hv.1 _ (List.getElem_mem e.isLt)).1⟩
  head := fun e => ⟨(I.edge e).head, (hv.1 _ (List.getElem_mem e.isLt)).2⟩
  capacity := fun e => ((I.edge e).upper - (I.edge e).lower).toNat
  cost := fun e => (I.edge e).cost

/-- Reinsert the lower-capacity vector. -/
def restore (I : Instance) (g : Fin I.m → ℝ) (e : Fin I.m) : ℝ :=
  ((I.edge e).lower : ℝ) + g e

/-- Remove the lower-capacity vector. -/
def shift (I : Instance) (f : Fin I.m → ℝ) (e : Fin I.m) : ℝ :=
  f e - ((I.edge e).lower : ℝ)

private theorem coefficient_cast (I : Instance) (e : Fin I.m) (v : Fin I.n) :
    (coefficient I e v : ℝ) = (I.edge e).b v := by
  simp [coefficient, Edge.b]

private theorem shifted_incidence (I : Instance) (hv : I.IsValid)
    (e : Fin I.m) (v : Fin I.n) :
    (shiftedGraph I hv).incidence e v = (I.edge e).b v := by
  simp [shiftedGraph, Circulation.incidence, Edge.b, Fin.ext_iff]

/-- Subtracting lower capacities subtracts their net flow from the demands. -/
theorem routes_restore_iff (I : Instance) (hv : I.IsValid) (g : Fin I.m → ℝ) :
    I.Routes (restore I g) ↔
      ∀ v, (shiftedGraph I hv).balance g v = (shiftedDemand I v : ℝ) := by
  have hb : ∀ v : Fin I.n, (∑ e, (I.edge e).b v * restore I g e) =
      (∑ e, (I.edge e).b v * ((I.edge e).lower : ℝ)) +
        (shiftedGraph I hv).balance g v := by
    intro v
    simp only [restore, mul_add, Finset.sum_add_distrib, Circulation.balance,
      shifted_incidence]
  have hd : ∀ v : Fin I.n, (shiftedDemand I v : ℝ) = (I.d v : ℝ) -
      ∑ e, (I.edge e).b v * ((I.edge e).lower : ℝ) := by
    intro v
    simp only [shiftedDemand, Int.cast_sub, Int.cast_sum, Int.cast_mul,
      coefficient_cast]
  constructor
  · intro h v
    have hr := h v
    rw [hb] at hr
    rw [hd]
    linarith only [hr]
  · intro h v
    have hr := h v
    rw [hd] at hr
    rw [hb]
    linarith only [hr]

/-- With consistent lower and upper capacities, restoration preserves exactly
all feasibility constraints of the general minimum-cost flow problem. -/
theorem feasible_restore_iff (I : Instance) (hv : I.IsValid)
    (hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper) (g : Fin I.m → ℝ) :
    I.IsFeasible (restore I g) ↔
      (∀ v, (shiftedGraph I hv).balance g v = (shiftedDemand I v : ℝ)) ∧
      ∀ e, 0 ≤ g e ∧ g e ≤ (shiftedGraph I hv).capacity e := by
  have hc : ∀ e : Fin I.m, ((shiftedGraph I hv).capacity e : ℝ) =
      ((I.edge e).upper : ℝ) - ((I.edge e).lower : ℝ) := by
    intro e
    dsimp only [shiftedGraph]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hcap e)),
      Int.cast_sub]
  unfold Instance.IsFeasible
  rw [routes_restore_iff I hv g]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro e
  rw [hc]
  dsimp only [restore]
  constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]

/-- Lower-capacity subtraction changes every feasible objective by the same
constant, so it preserves the ordering of candidate flows. -/
theorem cost_restore (I : Instance) (hv : I.IsValid) (g : Fin I.m → ℝ) :
    I.cost (restore I g) = I.cost (fun e => ((I.edge e).lower : ℝ)) +
      (shiftedGraph I hv).objective g := by
  simp only [Instance.cost, restore, mul_add, Finset.sum_add_distrib,
    Circulation.objective, shiftedGraph]

/-- The two changes of coordinates are inverse. -/
theorem restore_shift (I : Instance) (f : Fin I.m → ℝ) : restore I (shift I f) = f := by
  funext e
  simp [restore, shift]

/-- Inconsistent input capacities certify that no feasible flow exists. -/
theorem infeasible_of_upper_lt_lower (I : Instance) (e : Fin I.m)
    (h : (I.edge e).upper < (I.edge e).lower) : ∀ f, ¬ I.IsFeasible f := by
  intro f hf
  have hi : ((I.edge e).upper : ℝ) < ((I.edge e).lower : ℝ) :=
    (Int.cast_lt (R := ℝ)).mpr h
  exact (not_le_of_gt hi) (le_trans (hf.2 e).1 (hf.2 e).2)

end FlowReduction
end MinCostFlow.Scaling
