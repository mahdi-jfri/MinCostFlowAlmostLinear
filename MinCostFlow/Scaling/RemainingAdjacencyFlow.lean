module

public import MinCostFlow.Scaling.AdjacencyCounts
public import MinCostFlow.Scaling.ResidualReduction
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Flow represented by unconsumed adjacency entries

The unit-flow cycle extraction used in Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, removes one adjacency entry per traversed
arc. Its remaining edge counts form a nonnegative flow. Popping an arc
subtracts its incidence and cost exactly. A vertex with no outgoing entry
cannot have positive balance. These are the flow invariants of the scan.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The nonnegative flow encoded by the unused outgoing lists. -/
def adjacencyFlow (I : Circulation) (out : Fin I.n → List (Fin I.m)) (e : Fin I.m) : ℝ :=
  ((out (I.tail e)).count e : ℝ)

/-- Every encoded edge count is nonnegative. -/
theorem adjacencyFlow_nonneg (I : Circulation) (out : Fin I.n → List (Fin I.m)) (e : Fin I.m) :
    0 ≤ I.adjacencyFlow out e := Nat.cast_nonneg _

/-- The initial table represents exactly a nonnegative integral unit flow. -/
theorem adjacencyFlow_build (I : Circulation) (flow : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1) :
    I.adjacencyFlow (I.buildAdjacency flow) = fun e => (flow e : ℝ) := by
  funext e
  have hh := I.buildAdjacency_count_unit flow hf e
  unfold adjacencyFlow
  exact_mod_cast hh

/-- Removing the first stored arc subtracts precisely its unit edge vector. -/
theorem adjacencyFlow_pop (I : Circulation) (out : Fin I.n → List (Fin I.m))
    (v : Fin I.n) (e : Fin I.m) (rest : List (Fin I.m))
    (ho : out v = e :: rest) (he : I.tail e = v) (k : Fin I.m) :
    I.adjacencyFlow (Function.update out v rest) k =
      I.adjacencyFlow out k - (if k = e then 1 else 0) := by
  classical
  by_cases hk : k = e
  · subst k
    simp only [adjacencyFlow, he, Function.update_self, ho, List.count_cons,
      beq_self_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    ring
  · by_cases ht : I.tail k = v
    · simp [adjacencyFlow, ht, ho, hk, Ne.symm hk]
    · simp only [adjacencyFlow, Function.update_of_ne ht, hk, ↓reduceIte, sub_zero]

/-- Popping an arc subtracts its incidence from every vertex balance. -/
theorem adjacencyFlow_pop_balance (I : Circulation) (out : Fin I.n → List (Fin I.m))
    (v : Fin I.n) (e : Fin I.m) (rest : List (Fin I.m))
    (ho : out v = e :: rest) (he : I.tail e = v) (w : Fin I.n) :
    I.balance (I.adjacencyFlow (Function.update out v rest)) w =
      I.balance (I.adjacencyFlow out) w - I.incidence e w := by
  classical
  simp only [balance, I.adjacencyFlow_pop out v e rest ho he, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp [mul_ite]

/-- Popping an arc subtracts its integral cost from the unused objective. -/
theorem adjacencyFlow_pop_objective (I : Circulation) (out : Fin I.n → List (Fin I.m))
    (v : Fin I.n) (e : Fin I.m) (rest : List (Fin I.m))
    (ho : out v = e :: rest) (he : I.tail e = v) :
    I.objective (I.adjacencyFlow (Function.update out v rest)) =
      I.objective (I.adjacencyFlow out) - (I.cost e : ℝ) := by
  classical
  simp only [objective, I.adjacencyFlow_pop out v e rest ho he, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp [mul_ite]

/-- A vertex with no remaining outgoing entries has nonpositive balance. -/
theorem adjacencyFlow_balance_nonpos (I : Circulation) (out : Fin I.n → List (Fin I.m))
    (v : Fin I.n) (hv : out v = []) : I.balance (I.adjacencyFlow out) v ≤ 0 := by
  apply Finset.sum_nonpos
  intro e _
  by_cases ht : I.tail e = v
  · simp only [adjacencyFlow, ht, hv, List.count_nil, Nat.cast_zero, mul_zero, le_refl]
  · have ht' : v ≠ I.tail e := Ne.symm ht
    simp only [incidence, ht', ↓reduceIte, zero_sub, neg_mul]
    by_cases hh : v = I.head e
    · simp only [hh, ↓reduceIte, one_mul]
      exact neg_nonpos.mpr (I.adjacencyFlow_nonneg out e)
    · simp only [hh, ↓reduceIte, zero_mul, neg_zero, le_refl]

end MinCostFlow.Scaling.Circulation
