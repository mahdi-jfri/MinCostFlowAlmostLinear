module

public import MinCostFlow.Scaling.ShortestRoutingModel
import Mathlib.Tactic.Ring

/-!
# Numeric bounds for the shortest-routing correction

A feasible residual circulation has nonnegative coordinates bounded by
`n+1`. Augmenting the direct starting flow preserves its capacity bounds,
even though that starting flow has nonzero demands. Thus the integer
update is nonnegative and the unsigned scan's intermediate sum is at most
`n+2`. These facts supply the later machine augmentation and label calls.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- The direct starting vector has coordinates zero or one. -/
theorem shortestRoutingStart_le_one (J : Circulation) : ∀ e,J.shortestRoutingStart e ≤ 1 := by
  intro e
  refine Fin.addCases (fun e => ?_) (fun v => ?_) e <;>
    simp only [Circulation.shortestRoutingStart,Fin.addCases_left,Fin.addCases_right] <;> omega

/-- Every feasible integral residual correction has nonnegative coordinates
at most `n+1`, and its augmented routing has the same bounds. -/
theorem routingCorrection_bounds (J : Circulation)
    (delta : Fin ((J.m+J.n)+(J.m+J.n)) → ℤ)
    (hd : (J.shortestRoutingGraph.residual J.shortestRoutingStart).Feasible (fun e => (delta e : ℝ))) :
    (∀ e,0 ≤ delta e ∧ delta e ≤ (J.n+1 : ℕ)) ∧
    (∀ e,0 ≤ J.shortestRoutingStart e+delta (Fin.castAdd (J.m+J.n) e)-delta (Fin.natAdd (J.m+J.n) e) ∧
      J.shortestRoutingStart e+delta (Fin.castAdd (J.m+J.n) e)-delta (Fin.natAdd (J.m+J.n) e) ≤
        (J.shortestRoutingGraph.capacity e : ℤ)) := by
  have hcap := J.shortestRoutingGraph.residual_capacities_le J.shortestRoutingStart
    J.shortestRoutingStart_bounds (J.n+1) J.shortestRoutingGraph_capacities
  refine ⟨?_,?_⟩
  · intro e
    refine ⟨Int.cast_nonneg_iff.mp (hd.2 e).1,?_⟩
    have hh : (delta e : ℝ) ≤ ((J.n+1 : ℕ) : ℝ) :=
      (hd.2 e).2.trans (Nat.cast_le.mpr (hcap e))
    rw [← Int.cast_natCast] at hh
    exact Int.cast_le.mp hh
  · intro e
    have h := J.shortestRoutingGraph.augment_bounds J.shortestRoutingStart
      J.shortestRoutingStart_bounds (fun e => (delta e : ℝ)) hd e
    have heq : ((J.shortestRoutingStart e+delta (Fin.castAdd (J.m+J.n) e)-
        delta (Fin.natAdd (J.m+J.n) e) : ℤ) : ℝ) =
        J.shortestRoutingGraph.augment J.shortestRoutingStart (fun e => (delta e : ℝ)) e := by
      simp only [Int.cast_add,Int.cast_sub,Circulation.augment,Circulation.project]
      ring
    have hlo : 0 ≤ ((J.shortestRoutingStart e+delta (Fin.castAdd (J.m+J.n) e)-
        delta (Fin.natAdd (J.m+J.n) e) : ℤ) : ℝ) := by rw [heq]; exact h.1
    have hhi : ((J.shortestRoutingStart e+delta (Fin.castAdd (J.m+J.n) e)-
        delta (Fin.natAdd (J.m+J.n) e) : ℤ) : ℝ) ≤
        ((J.shortestRoutingGraph.capacity e : ℤ) : ℝ) := by
      rw [Int.cast_natCast,heq]
      exact h.2
    exact ⟨Int.cast_nonneg_iff.mp hlo,Int.cast_le.mp hhi⟩

/-- A fitting `n+2` budget covers all unsigned augmentation additions and
reverse coordinates for every feasible residual correction. -/
theorem routingCorrection_scan_bounds (J : Circulation) (w : ℕ)
    (delta : Fin ((J.m+J.n)+(J.m+J.n)) → ℤ)
    (hd : (J.shortestRoutingGraph.residual J.shortestRoutingStart).Feasible (fun e => (delta e : ℝ)))
    (hw : J.n+2 < 2^w) :
    ∀ e,(J.shortestRoutingStart e).toNat+(delta (Fin.castAdd (J.m+J.n) e)).toNat < 2^w ∧
      (delta (Fin.natAdd (J.m+J.n) e)).toNat < 2^w := by
  have hdelta := (routingCorrection_bounds J delta hd).1
  intro e
  have hstart : (J.shortestRoutingStart e).toNat ≤ 1 := by
    simpa only [Int.toNat_one] using Int.toNat_le_toNat (shortestRoutingStart_le_one J e)
  have hf : (delta (Fin.castAdd (J.m+J.n) e)).toNat ≤ J.n+1 := by
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat (hdelta (Fin.castAdd (J.m+J.n) e)).2
  have hr : (delta (Fin.natAdd (J.m+J.n) e)).toNat ≤ J.n+1 := by
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat (hdelta (Fin.natAdd (J.m+J.n) e)).2
  exact ⟨by omega,by omega⟩

end MinCostFlow.Scaling.Machine
