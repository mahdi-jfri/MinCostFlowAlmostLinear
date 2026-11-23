module

public import MinCostFlow.Scaling.LabelAccuracy
public import MinCostFlow.Scaling.RootedRoutingCoverage
public import MinCostFlow.Scaling.RootedRoutingTightness
public import MinCostFlow.Scaling.RootedShortestPaths

/-!
# Potentials returned by shortest-routing label propagation

The shortest-tree step in Lemma C.8 of Chen et al., arXiv:2203.00671v2,
Appendix C, is now combined: simple shortest paths give a bounded witness,
optimality makes every positive routing arc tight, and the unit demands
force all vertices to be visited. The computed integer labels therefore
equal negative shortest distances and satisfy every active arc inequality.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- An optimal rooted routing yields a feasible integral potential through
the actual counted label traversal. -/
theorem propagateLabels_potential (I : Circulation) (root : Fin I.n)
    (hclosed : ∀ v : Fin I.n, ∀ p : I.DirectedWalk v v, 0 ≤ p.cost)
    (hreach : ∀ v, Nonempty (I.DirectedWalk root v))
    (hcap : ∀ e, I.capacity e = 0 ∨ I.n ≤ I.capacity e)
    (flow : Fin I.m → ℤ)
    (hflow : ∀ e, 0 ≤ (flow e : ℝ) ∧ (flow e : ℝ) ≤ I.capacity e)
    (hbalance : ∀ v, I.balance (fun e => (flow e : ℝ)) v =
      (I.n : ℝ) * (if v = root then 1 else 0) - 1)
    (hopt : ∀ f : Fin I.m → ℝ,
      (∀ v, I.balance f v = (I.n : ℝ) * (if v = root then 1 else 0) - 1) →
      (∀ e, 0 ≤ f e ∧ f e ≤ I.capacity e) →
      I.objective (fun e => (flow e : ℝ)) ≤ I.objective f) :
    ∀ e, 0 < I.capacity e →
      (I.propagateLabels flow root).1.labels (I.tail e) -
        (I.propagateLabels flow root).1.labels (I.head e) ≤ I.cost e := by
  classical
  obtain ⟨d, hd, htri, hpaths⟩ := I.exists_rooted_distances root hclosed hreach
  choose paths hnodup hcost using hpaths
  have hbounds := I.rootedPathsFlow_bounds root paths hnodup hcap
  have hbal := I.rootedPathsFlow_balance root paths
  have hcompare := hopt (I.rootedPathsFlow root paths) hbal hbounds
  have htight := I.rooted_routing_tight root d hd htri paths hcost
    (fun e => (flow e : ℝ)) hbalance hflow hcompare
  have hseen := I.propagateLabels_all_seen flow root (fun e => (hflow e).1) hbalance
  have hlabels : ∀ v, (I.propagateLabels flow root).1.labels v = -d v := by
    intro v
    apply I.propagateLabels_accuracy flow root (fun v => -d v) (by rw [hd, neg_zero])
      (fun e he => htight e (Int.cast_pos.mpr he)) v (hseen v)
  intro e he
  rw [hlabels, hlabels]
  have hh := htri e he
  omega

end MinCostFlow.Scaling.Circulation
