module

public import MinCostFlow.Scaling.DirectedWalk

/-!
# Mapping walks when capacities change

The threshold graphs in the proof of Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, retain endpoints and costs while removing
arcs below a threshold. Any walk whose arcs remain active maps unchanged
into the new graph. The map preserves its cost, length, and edge counts.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.DirectedWalk
variable {I : Circulation}

/-- Interpret the same walk in a graph with new capacities keeping its arcs active. -/
def mapCapacities (capacity : Fin I.m → ℕ)
    (hactive : ∀ e, 0 < I.capacity e → 0 < capacity e) {a b : Fin I.n} :
    I.DirectedWalk a b → ({ I with capacity := capacity } : Circulation).DirectedWalk a b
  | .nil v => DirectedWalk.nil (I := { I with capacity := capacity }) v
  | .cons e he p => DirectedWalk.cons (I := { I with capacity := capacity }) e
      (hactive e he) (mapCapacities capacity hactive p)

/-- Capacity changes preserve costs along retained walks. -/
theorem cost_mapCapacities (capacity : Fin I.m → ℕ)
    (hactive : ∀ e, 0 < I.capacity e → 0 < capacity e) {a b : Fin I.n}
    (p : I.DirectedWalk a b) : (p.mapCapacities capacity hactive).cost = p.cost := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp only [mapCapacities, cost, ih]

/-- Capacity changes preserve each retained edge count. -/
theorem count_mapCapacities (capacity : Fin I.m → ℕ)
    (hactive : ∀ e, 0 < I.capacity e → 0 < capacity e) {a b : Fin I.n}
    (p : I.DirectedWalk a b) (e : Fin I.m) :
    (p.mapCapacities capacity hactive).count e = p.count e := by
  induction p with
  | nil => rfl
  | cons k he p ih => simp only [mapCapacities, count, ih]

end MinCostFlow.Scaling.Circulation.DirectedWalk
