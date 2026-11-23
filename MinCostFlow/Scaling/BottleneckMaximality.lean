module

public import MinCostFlow.Scaling.BottleneckSelection
public import MinCostFlow.Scaling.UsedCapacityWalkMap
import Mathlib.Data.Finset.Max

/-!
# Maximality of the selected bottleneck

The proof of Lemma C.10 of Chen et al., arXiv:2203.00671v2, Appendix C,
searches among the edge capacities. The least capacity on any negative
closed walk is one of these candidates, and the walk survives that threshold.
The finite search's rejected-suffix invariant therefore bounds this minimum
by its selected value. If no candidate was accepted, zero is optimal.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Every negative closed walk supplies an accepted edge-capacity candidate. -/
theorem negative_walk_accepted_capacity (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) (v : Fin I.n)
    (p : I.DirectedWalk v v) (hp : p.cost < 0) :
    let candidates := (sortCapacities (List.ofFn I.capacity)).1
    ∃ e : Fin I.m, ∃ j : ℕ, 0 < p.count e ∧ j < candidates.length ∧
      candidates.getD j 0 = I.capacity e ∧ I.bottleneckAccepts solve (I.capacity e) := by
  classical
  let S : Finset (Fin I.m) := Finset.univ.filter (fun e => 0 < p.count e)
  have hS : S.Nonempty := by
    cases p with
    | nil => simp only [Circulation.DirectedWalk.cost] at hp; omega
    | cons e he q =>
      exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simp only [Circulation.DirectedWalk.count, ↓reduceIte]; omega⟩⟩
  obtain ⟨e, he, hmin⟩ := S.exists_min_image I.capacity hS
  have hepos : 0 < p.count e := (Finset.mem_filter.mp he).2
  have hactive : ∀ a, 0 < p.count a → 0 < (I.bottleneckGraph (I.capacity e)).capacity a := by
    intro a ha
    change 0 < if 0 < I.capacity a ∧ I.capacity e ≤ I.capacity a then 1 else 0
    rw [ite_eq_left ⟨p.active_of_count_pos a ha,
      hmin a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)⟩]
    decide
  let q := Circulation.DirectedWalk.mapUsedCapacities (I := I)
    (I.bottleneckGraph (I.capacity e)).capacity p hactive
  have hqcost : q.cost < 0 := by
    rw [Circulation.DirectedWalk.cost_mapUsedCapacities]
    exact hp
  have hopt := I.bottleneckTest_optimal solve hsolve hc (I.capacity e)
  have haccept : I.bottleneckAccepts solve (I.capacity e) :=
    ((I.bottleneckGraph (I.capacity e)).optimal_integer_negative_iff _ hopt).mpr ⟨v, q, hqcost⟩
  have hmem : I.capacity e ∈ (sortCapacities (List.ofFn I.capacity)).1 :=
    (sortCapacities_perm _).mem_iff.mpr (List.mem_ofFn.mpr ⟨e, rfl⟩)
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨e, j, hepos, hj, ?_, haccept⟩
  simpa only [List.getD, List.getElem?_eq_getElem hj, Option.getD_some] using hjeq

/-- A selected bottleneck is at least the minimum capacity of every negative
closed walk. This is the maximal-bottleneck fact used in C.10's estimate. -/
theorem bottleneckSearch_bounds_negative (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) (u : ℕ) (f : Fin I.m → ℤ)
    (hbest : (bottleneckSearch solve I).value.best = some (u, f))
    (v : Fin I.n) (p : I.DirectedWalk v v) (hp : p.cost < 0) :
    ∃ e, 0 < p.count e ∧ I.capacity e ≤ u := by
  let candidates := (sortCapacities (List.ofFn I.capacity)).1
  let s := (bottleneckSearch solve I).value
  have hs := bottleneckSearch_selection solve hsolve I hc
  change s.lower = s.upper ∧ s.upper ≤ candidates.length ∧ _ at hs
  have hb := hs.2.2.2
  change (match s.best with | none => _ | some (u, f) => _) at hb
  rw [hbest] at hb
  change 0 < s.lower ∧ u = candidates.getD (s.lower - 1) 0 ∧ _ at hb
  have hrej : ∀ j, s.upper ≤ j → j < candidates.length →
      ¬ I.bottleneckAccepts solve (candidates.getD j 0) := hs.2.2.1
  obtain ⟨e, j, he, hj, hjeq, hjaccept⟩ := negative_walk_accepted_capacity solve hsolve I hc v p hp
  change j < candidates.length at hj
  have hjlow : j < s.lower := by
    by_contra hn
    have hh := hrej j (by omega) hj
    rw [hjeq] at hh
    exact hh hjaccept
  have hib : s.lower - 1 < candidates.length := by omega
  have hsort : candidates.Pairwise (· ≤ ·) := sortCapacities_sorted (List.ofFn I.capacity)
  have hle := hsort.rel_get_of_le (a := ⟨j, hj⟩) (b := ⟨s.lower - 1, hib⟩)
    (by change j ≤ s.lower - 1; omega)
  have hle' : candidates.getD j 0 ≤ candidates.getD (s.lower - 1) 0 := by
    simpa only [List.getD, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hib,
      Option.getD_some, List.get_eq_getElem] using hle
  exact ⟨e, he, by rw [hjeq, ← hb.2.1] at hle'; exact hle'⟩

/-- If the search accepts no capacity, the original circulation optimum is zero. -/
theorem bottleneckSearch_none_optimal (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10))
    (hbest : (bottleneckSearch solve I).value.best = none) : I.Optimal (fun _ => 0) := by
  have hs := bottleneckSearch_selection solve hsolve I hc
  have hb := hs.2.2.2
  rw [hbest] at hb
  apply I.zero_optimal_of_closed_nonneg
  intro v p
  by_contra hn
  have hp : p.cost < 0 := by omega
  obtain ⟨e, j, _, hj, hjeq, haccept⟩ := negative_walk_accepted_capacity solve hsolve I hc v p hp
  have hh := hs.2.2.1 j (by omega) hj
  rw [hjeq] at hh
  exact hh haccept

end MinCostFlow.Scaling
