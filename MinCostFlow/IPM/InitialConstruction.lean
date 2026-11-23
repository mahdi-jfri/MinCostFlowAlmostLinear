module

public import MinCostFlow.IPM.RemoveFixed
public import MinCostFlow.IPM.CapacityPreprocessing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The auxiliary-vertex construction

Lemma 4.12 (page 31) of Chen et al., arXiv:2203.00671v2, is proved in Appendix B.1 (page 92).
After deleting fixed edges, start the retained edges at their midpoints.
For each nonzero midpoint demand deficit add an edge to one new vertex,
with zero lower capacity, twice the deficit magnitude as upper capacity,
and midpoint flow equal to the deficit magnitude. Integer twice-deficits
make the capacities integral. Directions below use the tail-positive
incidence convention fixed by `Instance.Routes`.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Twice the demand missing at a vertex of the original midpoint flow.
The expression is integral even if the midpoint flow is half-integral. -/
def twiceDeficit (I : Instance) (v : Fin I.n) : ℤ :=
  2*I.d v - ∑ e, incidenceInt (I.edge e) v*((I.edge e).lower+(I.edge e).upper)

/-- Only vertices with nonzero deficit receive an auxiliary edge. -/
def deficitVertices (I : Instance) : Finset (Fin I.n) :=
  Finset.univ.filter fun v => twiceDeficit I v ≠ 0

/-- The increasing enumeration of vertices receiving an auxiliary edge. -/
def deficitIndex (I : Instance) : Fin (deficitVertices I).card ≃ {v // v ∈ deficitVertices I} :=
  ((deficitVertices I).orderIsoOfFin rfl).toEquiv

/-- An auxiliary edge routing a signed deficit `z/2` at `v`. Its upper
capacity is `|z|`, and its midpoint flow is `|z|/2`. -/
def starEdge (n : ℕ) (v : Fin n) (z K : ℤ) : Edge :=
  if 0 ≤ z then ⟨v, n, 0, |z|, K⟩ else ⟨n, v, 0, |z|, K⟩

/-- The edge array of the augmented instance: retained original edges,
followed by auxiliary edges. -/
def initialEdgeArray (I : Instance) (K : ℤ) :
    Fin ((freeEdges I).card+(deficitVertices I).card) → Edge :=
  Fin.addCases (freeEdgeArray I) (fun j =>
    starEdge I.n (deficitIndex I j).1 (twiceDeficit I (deficitIndex I j).1) K)

/-- The reduced original demands and zero demand at the new vertex. -/
def initialDemands (I : Instance) : Fin (I.n+1) → ℤ :=
  Fin.lastCases 0 (freeDemands I)

/-- The midpoint array flow on retained and auxiliary edges. -/
def initialArrayFlow (I : Instance) :
    Fin ((freeEdges I).card+(deficitVertices I).card) → ℝ :=
  Fin.addCases (fun j => (((freeEdgeArray I j).lower : ℝ)+(freeEdgeArray I j).upper)/2)
    (fun j => |(twiceDeficit I (deficitIndex I j).1 : ℝ)|/2)

/-- The augmented instance of Lemma 4.12 (page 31), with a supplied integral
artificial-edge penalty `K`. The source chooses `K = 4mU²`. -/
def initialInstance (I : Instance) (K : ℤ) : Instance :=
  instanceOfArrays (I.n+1) ((freeEdges I).card+(deficitVertices I).card)
    (initialEdgeArray I K) (initialDemands I)

/-- The initial flow `f^init` on the augmented instance. -/
def initialFlow (I : Instance) (K : ℤ) : Fin (initialInstance I K).m → ℝ :=
  flowOfArray (initialEdgeArray I K) (initialDemands I) (initialArrayFlow I)

/-- The constructed instance has one additional vertex. -/
theorem initialInstance_n (I : Instance) (K : ℤ) : (initialInstance I K).n = I.n+1 := rfl

/-- Its edge count is exactly retained edges plus nonzero deficits. -/
theorem initialInstance_m (I : Instance) (K : ℤ) :
    (initialInstance I K).m = (freeEdges I).card+(deficitVertices I).card :=
  instanceOfArrays_m _ _ _ _

/-- The real twice-deficit is twice the missing midpoint demand. -/
theorem twiceDeficit_cast (I : Instance) (v : Fin I.n) :
    (twiceDeficit I v : ℝ) = 2*((I.d v : ℝ)-∑ e, (I.edge e).b v*midpointFlow I e) := by
  simp only [twiceDeficit, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_sum,
    incidenceInt_cast, Int.cast_add, midpointFlow, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- An auxiliary edge contributes exactly its signed deficit at its old
endpoint, and zero at every other old vertex. -/
theorem starEdge_old_contribution (n : ℕ) (v w : Fin n) (z K : ℤ) :
    (starEdge n v z K).b w*(|(z : ℝ)|/2) = if w = v then (z : ℝ)/2 else 0 := by
  have hwn : (w : ℕ) ≠ n := Nat.ne_of_lt w.2
  by_cases hw : w = v
  · subst w
    by_cases hz : 0 ≤ z
    · have hz' : (0 : ℝ) ≤ z := by exact_mod_cast hz
      simp only [starEdge, hz, ↓reduceIte, Edge.b, hwn,
        sub_zero, one_mul, abs_of_nonneg hz']
    · have hz' : (z : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hz)
      simp only [starEdge, hz, ↓reduceIte, Edge.b, hwn,
        zero_sub, abs_of_neg hz']
      ring
  · have hwv : (w : ℕ) ≠ v := by intro he; exact hw (Fin.ext he)
    by_cases hz : 0 ≤ z <;>
      simp only [starEdge, hz, ↓reduceIte, Edge.b, hwn, hwv, sub_self, zero_mul, hw]

/-- At the new vertex the auxiliary edge contributes the negative deficit. -/
theorem starEdge_new_contribution (n : ℕ) (v : Fin n) (z K : ℤ) :
    (starEdge n v z K).b n*(|(z : ℝ)|/2) = -(z : ℝ)/2 := by
  have hnv : n ≠ (v : ℕ) := (Nat.ne_of_lt v.2).symm
  by_cases hz : 0 ≤ z
  · have hz' : (0 : ℝ) ≤ z := by exact_mod_cast hz
    simp only [starEdge, hz, ↓reduceIte, Edge.b, hnv, zero_sub,
      abs_of_nonneg hz']
    ring
  · have hz' : (z : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hz)
    simp only [starEdge, hz, ↓reduceIte, Edge.b, hnv, sub_zero,
      one_mul, abs_of_neg hz']


end MinCostFlow.IPM
