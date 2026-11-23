module

public import MinCostFlow.Scaling.CapacityWalkMap

/-!
# Mapping a walk when only its used arcs survive

The minimum-capacity threshold in Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, retains every arc of the chosen cycle but may
remove other arcs. The same walk maps into this threshold graph by checking
only positive edge counts. Its integral cost is unchanged.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.DirectedWalk
variable {I : Circulation}

/-- Interpret a walk under new capacities that retain every arc it uses. -/
def mapUsedCapacities (capacity : Fin I.m → ℕ) {a b : Fin I.n}
    (p : I.DirectedWalk a b) (hactive : ∀ e, 0 < p.count e → 0 < capacity e) :
    ({ I with capacity := capacity } : Circulation).DirectedWalk a b :=
  match p with
  | .nil v => DirectedWalk.nil (I := { I with capacity := capacity }) v
  | .cons e he q => DirectedWalk.cons (I := { I with capacity := capacity }) e
      (hactive e (by simp only [count, ↓reduceIte]; omega))
      (mapUsedCapacities capacity q (fun k hk => hactive k (by
        simp only [count]
        split <;> omega)))

/-- Retaining a walk's used arcs preserves its cost. -/
theorem cost_mapUsedCapacities (capacity : Fin I.m → ℕ) {a b : Fin I.n}
    (p : I.DirectedWalk a b) (hactive : ∀ e, 0 < p.count e → 0 < capacity e) :
    (p.mapUsedCapacities capacity hactive).cost = p.cost := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp only [mapUsedCapacities, cost, ih]

end MinCostFlow.Scaling.Circulation.DirectedWalk
