module

public import MinCostFlow.IPM.Machine.InitialEndpointSums
public import MinCostFlow.IPM.InitialConstruction
public import MinCostFlow.Scaling.CirculationInstance
import Mathlib.Tactic.Ring

/-!
# Identifying the signed routing deficit from endpoint tables

Lemma 4.12 of Chen et al., arXiv:2203.00671v2 (page 31,
Appendix B.1 page 92), adds auxiliary edges for the midpoint deficits.
The bounded circulation solver has zero demands and zero lower bounds.
Thus incoming capacity minus outgoing capacity equals exactly the
integer `twiceDeficit` in the existing initialization construction.
This file proves that identity and the correspondence with the scan's
prefix sums, without changing the source's construction or signs.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Scaling

/-- Total upper capacity incident as a tail at a named vertex. -/
def outgoingCapacity (J : Circulation) (v : ℕ) : ℕ :=
  ∑ e : Fin J.m, if (J.tail e : ℕ) = v then J.capacity e else 0

/-- Total upper capacity incident as a head at a named vertex. -/
def incomingCapacity (J : Circulation) (v : ℕ) : ℕ :=
  ∑ e : Fin J.m, if (J.head e : ℕ) = v then J.capacity e else 0

/-- The scan's natural-index prefix total agrees with the finite-edge
sum after all input edges have been read. -/
theorem initialEndpointSum_eq_fin (endpoint weight : ℕ → ℕ) (m v : ℕ) :
    initialEndpointSum endpoint weight m v =
      ∑ e : Fin m, if endpoint e.val = v then weight e.val else 0 :=
  (Fin.sum_univ_eq_sum_range _ m).symm

/-- The two unsigned tables determine the exact signed doubled deficit.
A self-loop contributes once to each side and therefore cancels. -/
theorem twiceDeficit_eq_capacity_difference (J : Circulation) (v : Fin J.n) :
    twiceDeficit J.toInstance v = (incomingCapacity J v : ℤ)-(outgoingCapacity J v : ℤ) := by
  have hd : J.toInstance.d v = 0 := by simp [Instance.d]
  have hsum :
      (∑ e : Fin J.toInstance.m,
        incidenceInt (J.toInstance.edge e) v *
          ((J.toInstance.edge e).lower+(J.toInstance.edge e).upper)) =
      ∑ e : Fin J.m,
        ((if (v : ℕ) = J.tail e then (1 : ℤ) else 0)-
          (if (v : ℕ) = J.head e then (1 : ℤ) else 0))*(J.capacity e : ℤ) := by
    simp only [Circulation.toInstance_edge,Circulation.inputEdge,incidenceInt,zero_add]
    exact Equiv.sum_comp J.inputIndex (fun e : Fin J.m =>
      ((if (v : ℕ) = J.tail e then (1 : ℤ) else 0)-
        (if (v : ℕ) = J.head e then (1 : ℤ) else 0))*(J.capacity e : ℤ))
  rw [twiceDeficit,hd,mul_zero,zero_sub,hsum]
  simp only [incomingCapacity,outgoingCapacity,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
  rw [← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [eq_comm (a := (v : ℕ)) (b := (J.tail e : ℕ)),
    eq_comm (a := (v : ℕ)) (b := (J.head e : ℕ))]
  split_ifs <;> ring


/-- Exact endpoint decoding suffices to identify the output table. -/
theorem initialEndpointSum_outgoing (J : Circulation) (endpoint weight : ℕ → ℕ)
    (he : ∀ e : Fin J.m, endpoint e.val = J.tail e)
    (hc : ∀ e : Fin J.m, weight e.val = J.capacity e) (v : ℕ) :
    initialEndpointSum endpoint weight J.m v = outgoingCapacity J v := by
  rw [initialEndpointSum_eq_fin]
  apply Finset.sum_congr rfl
  intro e _
  rw [he e,hc e]

/-- The second scan identifies the incoming table, with the same capacity
words and the head fields instead of the tail fields. -/
theorem initialEndpointSum_incoming (J : Circulation) (endpoint weight : ℕ → ℕ)
    (he : ∀ e : Fin J.m, endpoint e.val = J.head e)
    (hc : ∀ e : Fin J.m, weight e.val = J.capacity e) (v : ℕ) :
    initialEndpointSum endpoint weight J.m v = incomingCapacity J v := by
  rw [initialEndpointSum_eq_fin]
  apply Finset.sum_congr rfl
  intro e _
  rw [he e,hc e]

/-- An outgoing endpoint table entry never exceeds the total input capacity. -/
theorem outgoingCapacity_le_total (J : Circulation) (v : ℕ) :
    outgoingCapacity J v ≤ ∑ e : Fin J.m, J.capacity e := by
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> omega

/-- The same fit bound holds for the incoming table. -/
theorem incomingCapacity_le_total (J : Circulation) (v : ℕ) :
    incomingCapacity J v ≤ ∑ e : Fin J.m, J.capacity e := by
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> omega

end MinCostFlow.IPM.Machine
