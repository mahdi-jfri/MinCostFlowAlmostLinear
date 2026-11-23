module

public import MinCostFlow.Scaling.Residual
public import MinCostFlow.Scaling.SolverContract
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.NormNum

/-!
# The two residual edge blocks

Appendix C of Chen et al., arXiv:2203.00671v2, defines the forward residual
capacity as `u-f`, and the reverse capacity as `f` with negated cost.
The formal model retains zero-capacity slots. This file identifies the two
ordered five-word blocks with exactly `Circulation.residual.solverWords`
and gives the canonical sign computation used by the reverse-block program.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine

/-- One forward or reverse residual edge in the shared circulation layout. -/
def residualEdgeWords (J : Circulation) (f : Fin J.m → ℤ) (reverse : Bool)
    (e : Fin J.m) : List ℕ :=
  if reverse then [J.head e, J.tail e, (f e).toNat,
    if -J.cost e < 0 then 1 else 0, (J.cost e).natAbs]
  else [J.tail e, J.head e, ((J.capacity e : ℤ) - f e).toNat,
    if J.cost e < 0 then 1 else 0, (J.cost e).natAbs]

/-- Every residual edge occupies five words in either direction. -/
theorem residualEdgeWords_length (J : Circulation) (f : Fin J.m → ℤ) (reverse : Bool)
    (e : Fin J.m) : (residualEdgeWords J f reverse e).length = 5 := by
  cases reverse <;> rfl

/-- A selected list of residual edges uses five words per edge. -/
theorem residualRecords_length (J : Circulation) (f : Fin J.m → ℤ) (reverse : Bool)
    (es : List (Fin J.m)) :
    (es.flatMap (residualEdgeWords J f reverse)).length = 5 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.flatMap_cons, List.length_append, residualEdgeWords_length, ih, List.length_cons]
    omega

/-- Negating a cost flips a nonzero sign and keeps canonical zero unsigned.
The magnitude test is an ordinary machine comparison. -/
theorem negatedCostSign_eq (z : ℤ) :
    (if -z < 0 then 1 else 0 : ℕ) =
      (1 - (if z < 0 then 1 else 0)) * (if 0 < z.natAbs then 1 else 0) := by
  by_cases hz : z < 0 <;> by_cases hn : -z < 0 <;> by_cases hm : 0 < z.natAbs <;>
    simp only [hz, hn, hm, ↓reduceIte] <;> omega

/-- The unsigned subtraction instruction gives the forward residual
capacity whenever the current integral flow lies in its capacity interval. -/
theorem residual_capacity_sub (u : ℕ) (f : ℤ) (hf : 0 ≤ f) (hu : f ≤ u) :
    u - f.toNat = ((u : ℤ) - f).toNat := by omega

private theorem residual_castLE {m n : ℕ} (h : m ≤ m + n) (e : Fin m) :
    Fin.castLE h e = Fin.castAdd n e := by
  apply Fin.ext
  rfl

/-- The residual model's common encoding contains all forward slots before
all reverse slots, with the original vertex set. -/
theorem residual_solverWords (J : Circulation) (f : Fin J.m → ℤ) :
    (J.residual f).solverWords = J.n :: (J.m + J.m) ::
      ((List.ofFn (residualEdgeWords J f false)).flatten ++
        (List.ofFn (residualEdgeWords J f true)).flatten) := by
  unfold Circulation.solverWords
  rw [List.flatMap, ← List.ofFn_eq_map, List.ofFn_add, List.flatten_append]
  congr 1
  congr 1
  congr 1 <;> apply congrArg List.flatten <;> apply congrArg List.ofFn <;> funext e <;>
    simp only [Circulation.solverEdgeWords, Circulation.residual, residual_castLE,
      Fin.addCases_left, Fin.addCases_right, residualEdgeWords, Bool.false_eq_true,
      ↓reduceIte, Int.natAbs_neg]

end MinCostFlow.Scaling.Machine
