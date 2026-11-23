module

public import MinCostFlow.Scaling.DemandReduction
public import MinCostFlow.Scaling.SolverContract
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

/-!
# Layout of artificial demand arcs

The demand-instance reduction of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, adds one root vertex. The first artificial block goes
from the root to each old vertex, with positive demand capacity. The second
block reverses these arcs and uses negative demand capacity. Both blocks
have cost minus one. These definitions describe their common five-word
solver records in exactly the model's vertex order.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine

/-- One artificial arc, selecting its direction and unsigned demand part. -/
def demandArcWords (root : ℕ) (negative : Bool) (vertex : ℕ) (z : ℤ) : List ℕ :=
  if negative then [vertex, root, (-z).toNat, 1, 1]
  else [root, vertex, z.toNat, 1, 1]

/-- Consecutive artificial arcs for a stored signed demand list. -/
def demandArcRecords (root : ℕ) (negative : Bool) (vertex : ℕ) (zs : List ℤ) : List ℕ :=
  (zs.zipIdx vertex).flatMap fun p => demandArcWords root negative p.2 p.1

/-- Every artificial arc occupies five solver words. -/
theorem demandArcWords_length (root vertex : ℕ) (negative : Bool) (z : ℤ) :
    (demandArcWords root negative vertex z).length = 5 := by
  cases negative <;> rfl

/-- An empty demand block produces no artificial records. -/
theorem demandArcRecords_nil (root vertex : ℕ) (negative : Bool) :
    demandArcRecords root negative vertex [] = [] := rfl

/-- The artificial-arc scan keeps the original demand order. -/
theorem demandArcRecords_cons (root vertex : ℕ) (negative : Bool) (z : ℤ) (zs : List ℤ) :
    demandArcRecords root negative vertex (z :: zs) =
      demandArcWords root negative vertex z ++ demandArcRecords root negative (vertex + 1) zs := by
  simp only [demandArcRecords, List.zipIdx_cons, List.flatMap_cons]

/-- Each demand contributes exactly one artificial edge record. -/
theorem demandArcRecords_length (root vertex : ℕ) (negative : Bool) (zs : List ℤ) :
    (demandArcRecords root negative vertex zs).length = 5 * zs.length := by
  induction zs generalizing vertex with
  | nil => rfl
  | cons z zs ih =>
    rw [demandArcRecords_cons, List.length_append, demandArcWords_length, ih, List.length_cons]
    omega

/-- On a vertex-indexed vector, the record scan agrees with the model's
increasing vertex order. -/
theorem demandArcRecords_ofFn (root vertex : ℕ) (negative : Bool)
    {n : ℕ} (d : Fin n → ℤ) :
    demandArcRecords root negative vertex (List.ofFn d) =
      (List.ofFn fun v => demandArcWords root negative (vertex + v.val) (d v)).flatten := by
  induction n generalizing vertex with
  | zero => simp [demandArcRecords]
  | succ n ih =>
    rw [List.ofFn_succ, demandArcRecords_cons, ih]
    conv_rhs => rw [List.ofFn_succ]
    simp only [List.flatten_cons, Fin.val_zero, Nat.add_zero]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext v
    have he : vertex + 1 + v.val = vertex + v.succ.val := by simp only [Fin.val_succ]; omega
    rw [he]

/-- Old edges of the feasibility circulation keep capacities and endpoints
but receive zero costs. -/
def demandOldEdgeWords (J : Circulation) (e : Fin J.m) : List ℕ :=
  [J.tail e, J.head e, J.capacity e, 0, 0]

/-- The old feasibility block still uses five words per edge. -/
theorem demandOldRecords_length (J : Circulation) (es : List (Fin J.m)) :
    (es.flatMap (demandOldEdgeWords J)).length = 5 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, demandOldEdgeWords,
      List.length_cons, List.length_nil, ih]
    omega

private theorem castLE_eq_castAdd {m n : ℕ} (h : m ≤ m + n) (e : Fin m) :
    Fin.castLE h e = Fin.castAdd n e := by
  apply Fin.ext
  rfl

/-- The two artificial blocks and zero-cost old block are exactly the
solver layout of the model's feasibility circulation. -/
theorem demandInstance_solverWords (J : Circulation) (d : Fin J.n → ℤ) :
    (J.demandInstance d).solverWords =
      (J.n + 1) :: (J.m + (J.n + J.n)) ::
        ((List.ofFn (demandOldEdgeWords J)).flatten ++
          (demandArcRecords J.n false 0 (List.ofFn d) ++
            demandArcRecords J.n true 0 (List.ofFn d))) := by
  rw [demandArcRecords_ofFn, demandArcRecords_ofFn]
  simp only [Nat.zero_add]
  unfold Circulation.solverWords
  rw [List.flatMap, ← List.ofFn_eq_map]
  rw [List.ofFn_add]
  simp only [List.flatten_append]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply congrArg List.ofFn
    funext e
    simp only [Circulation.solverEdgeWords, Circulation.demandInstance,
      castLE_eq_castAdd, Fin.addCases_left, demandOldEdgeWords, Fin.val_castSucc]
    norm_num
  · rw [List.ofFn_add, List.flatten_append]
    congr 1 <;> apply congrArg List.flatten <;> apply congrArg List.ofFn <;> funext v <;>
      simp only [Circulation.solverEdgeWords, Circulation.demandInstance, castLE_eq_castAdd,
        Fin.addCases_left, Fin.addCases_right, demandArcWords, Bool.false_eq_true,
        ↓reduceIte, Fin.val_castSucc, Fin.val_last] <;> norm_num

end MinCostFlow.Scaling.Machine
