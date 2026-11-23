module

public import MinCostFlow.Scaling.CycleScanCorrectness
public import MinCostFlow.Scaling.Scatter
public import MinCostFlow.Scaling.CapacitySolverModel
import Mathlib.Tactic.Ring

/-!
# Scattering a closed edge-simple walk into a flow

Lemma C.10 of Chen et al., arXiv:2203.00671v2, Appendix C, sends the
selected bottleneck amount around its returned negative cycle. The actual
model writes that integer amount into each returned edge slot. For an
edge-simple closed walk, these writes equal its scaled edge-count flow.
Conservation and capacity bounds therefore follow directly from the walk.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Scattering a constant on an edge-simple walk agrees with its edge counts. -/
theorem scatter_closed_walk (I : Circulation) {v : Fin I.n} (p : I.DirectedWalk v v)
    (hp : ∀ e, p.count e ≤ 1) (u : ℤ) :
    (Scatter.withWork (fun _ : Fin I.m => (0 : ℤ)) (p.edges.map (fun e => (e, u)))).1 =
      fun e => u * (p.count e : ℤ) := by
  classical
  rw [Scatter.withWork_value]
  have hnd : p.edges.Nodup := by
    rw [List.nodup_iff_count_le_one]
    intro e
    rw [p.count_edges]
    exact hp e
  funext e
  by_cases he : e ∈ p.edges
  · have hc : p.count e = 1 := by rw [← p.count_edges]; exact List.count_eq_one_of_mem hnd he
    have hlookup := Scatter.lookup (fun _ : Fin I.m => (0 : ℤ)) (p.edges.map (fun e => (e, u)))
      (by
        rw [List.map_map]
        change (p.edges.map id).Nodup
        rw [List.map_id]
        exact hnd)
      e u (List.mem_map.mpr ⟨e, he, rfl⟩)
    rw [hlookup, hc, Nat.cast_one, mul_one]
  · have hc : p.count e = 0 := by rw [← p.count_edges]; exact List.count_eq_zero_of_not_mem he
    rw [Scatter.unchanged]
    · rw [hc, Nat.cast_zero, mul_zero]
    · intro entry hentry heq
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hentry
      exact he (heq ▸ ha)

/-- Scaling a closed edge-simple walk by an admissible nonnegative amount
produces a feasible circulation. -/
theorem DirectedWalk.scaled_counts_feasible {I : Circulation} {v : Fin I.n}
    (p : I.DirectedWalk v v) (hp : ∀ e, p.count e ≤ 1) (u : ℕ)
    (hu : ∀ e, 0 < p.count e → u ≤ I.capacity e) :
    I.Feasible (fun e => (u : ℝ) * (p.count e : ℝ)) := by
  constructor
  · intro w
    rw [I.balance_const_mul, p.balance_count, sub_self, mul_zero]
  · intro e
    dsimp only
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · by_cases hz : p.count e = 0
      · rw [hz, Nat.cast_zero, mul_zero]
        exact Nat.cast_nonneg _
      · have hone : p.count e = 1 := by have hh := hp e; omega
        rw [hone, Nat.cast_one, mul_one]
        exact_mod_cast hu e (Nat.pos_of_ne_zero hz)

/-- Scaling the edge counts multiplies the integral walk cost by the same amount. -/
theorem DirectedWalk.objective_scaled_counts {I : Circulation} {v : Fin I.n}
    (p : I.DirectedWalk v v) (u : ℕ) :
    I.objective (fun e => (u : ℝ) * (p.count e : ℝ)) = (u : ℝ) * (p.cost : ℝ) := by
  simp only [objective]
  have he : (∑ e, (I.cost e : ℝ) * ((u : ℝ) * (p.count e : ℝ))) =
      (u : ℝ) * I.objective (fun e => (p.count e : ℝ)) := by
    simp only [objective, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he, p.objective_count]

end MinCostFlow.Scaling.Circulation
