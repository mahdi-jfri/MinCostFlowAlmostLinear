module

public import MinCostFlow.Scaling.BottleneckFlow
public import MinCostFlow.Scaling.BottleneckMaximality
public import MinCostFlow.Scaling.BottleneckObjective
public import MinCostFlow.Scaling.CycleScatter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Approximation from the selected extracted cycle

The final estimate in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, sends the selected bottleneck around a negative cycle. The
proved unit-flow scan supplies a closed edge-simple walk, and its scatter
has cost at most minus that bottleneck. Maximality bounds every feasible
real circulation below by minus `m^12` times the same bottleneck. This file
joins these statements for the exact returned edge list and table writes.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Scattering the selected extracted cycle gives a negative feasible
`m^12` approximation against every feasible real circulation. -/
theorem selected_cycle_flow_approximation (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) (u : ℕ) (f : Fin I.m → ℤ)
    (hbest : (bottleneckSearch solve I).value.best = some (u, f))
    (es : List (Fin I.m)) (hes : (I.extractCycleModel f).1.result = some es)
    (v : Fin I.n) (p : I.DirectedWalk v v) (hedges : p.edges = es) (hp : ∀ e, p.count e ≤ 1) :
    let F := (Scatter.withWork (fun _ : Fin I.m => (0 : ℤ)) (es.map (fun e => (e, (u : ℤ))))).1
    I.Feasible (fun e => (F e : ℝ)) ∧ I.objective (fun e => (F e : ℝ)) < 0 ∧
      ∀ g : Fin I.m → ℝ, I.Feasible g →
        ((I.m ^ 12 : ℕ) : ℝ) * I.objective (fun e => (F e : ℝ)) ≤ I.objective g := by
  have hs := bottleneckSearch_selection solve hsolve I hc
  have hb := hs.2.2.2
  rw [hbest] at hb
  have htest : (I.bottleneckGraph u).Optimal (fun e => (f e : ℝ)) := by
    rw [hb.2.2.1]
    exact I.bottleneckTest_optimal solve hsolve hc u
  have hf := I.bottleneckGraph_feasible u (fun e => (f e : ℝ)) htest.1
  have hnegative : I.objective (fun e => (f e : ℝ)) < 0 := by
    have hi : I.integerObjective f < 0 := hb.2.2.2
    rw [← I.integerObjective_cast]
    exact_mod_cast hi
  have hcycles : ∀ w : Fin I.n, ∀ q : I.DirectedWalk w w,
      (∀ e, q.count e ≤ 1) → q.cost < 0 → ∃ e, 0 < q.count e ∧ I.capacity e ≤ u := by
    intro w q _ hq
    exact bottleneckSearch_bounds_negative solve hsolve I hc u f hbest w q hq
  have hbound := I.objective_ge_neg_pow_twelve_mul u hc hcycles
  have hup : 0 < u := by
    by_contra hn
    have hu : u = 0 := by omega
    have hh := hbound (fun e => (f e : ℝ)) hf
    rw [hu, Nat.cast_zero, mul_zero] at hh
    linarith only [hh, hnegative]
  let F := (Scatter.withWork (fun _ : Fin I.m => (0 : ℤ)) (es.map (fun e => (e, (u : ℤ))))).1
  have hF : F = fun e => (u : ℤ) * (p.count e : ℤ) := by
    unfold F
    rw [← hedges]
    exact I.scatter_closed_walk p hp (u : ℤ)
  have hcast : (fun e => (F e : ℝ)) = fun e => (u : ℝ) * (p.count e : ℝ) := by
    rw [hF]
    funext e
    simp only [Int.cast_mul, Int.cast_natCast]
  have hcap : ∀ e, 0 < p.count e → u ≤ I.capacity e := by
    intro e he
    have hmem : e ∈ es := by
      rw [← hedges]
      apply List.count_pos_iff.mp
      rw [p.count_edges]
      exact he
    have hpos := I.extractCycleModel_positive f es hes e hmem
    exact (I.bottleneckGraph_pos_flow u (fun e => (f e : ℝ)) htest.1 e (Int.cast_pos.mpr hpos)).2
  have hfeas : I.Feasible (fun e => (F e : ℝ)) := by
    rw [hcast]
    exact p.scaled_counts_feasible hp u hcap
  have hcost : I.objective (fun e => (F e : ℝ)) = (u : ℝ) * (p.cost : ℝ) := by
    rw [hcast]
    exact p.objective_scaled_counts u
  have hpneg : p.cost < 0 := by
    rw [← p.sum_cost_edges, hedges]
    exact I.extractCycleModel_negative f es hes
  have hcostle : I.objective (fun e => (F e : ℝ)) ≤ -(u : ℝ) := by
    have hi : p.cost ≤ -1 := by omega
    have hr : (p.cost : ℝ) ≤ -1 := by exact_mod_cast hi
    rw [hcost]
    have hh := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) u)
    simpa only [mul_neg, mul_one] using hh
  refine ⟨hfeas, ?_, ?_⟩
  · have hu : (0 : ℝ) < u := Nat.cast_pos.mpr hup
    linarith only [hcostle, hu]
  · intro g hg
    have hh := mul_le_mul_of_nonneg_left hcostle (Nat.cast_nonneg (α := ℝ) (I.m ^ 12))
    have hl := hbound g hg
    simp only [mul_neg] at hh
    exact le_trans hh (by simpa only [neg_mul] using hl)

end MinCostFlow.Scaling
