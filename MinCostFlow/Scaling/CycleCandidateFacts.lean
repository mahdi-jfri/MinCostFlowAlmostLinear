module

public import MinCostFlow.Scaling.ApproximationModel
public import MinCostFlow.Scaling.ObjectiveScanFacts

/-!
# Unsigned cycle-candidate values

The approximation writes one nonnegative bottleneck amount at each
returned edge. Its unsigned scatter is exactly the integer scatter after
casting. Each resulting coordinate is bounded by that amount, so the
objective scan's absolute-product budget is at most `m*C*u`.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- Overwriting with a bounded constant preserves a coordinatewise bound. -/
theorem scatter_constant_le {n : ℕ} (s : Fin n → ℕ) (es : List (Fin n)) (u : ℕ)
    (hs : ∀ e,s e≤u) : ∀ e,Scatter.write s (es.map (fun e => (e,u))) e≤u := by
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih =>
    apply ih
    intro k
    by_cases heq : k=e
    · subst k
      exact (Function.update_self _ _ _).le
    · simpa only [Function.update_of_ne heq] using hs k

/-- The unsigned constant scatter casts exactly to the integer candidate
computed by the approximation model. -/
theorem scatter_constant_cast {n : ℕ} (es : List (Fin n)) (u : ℕ) :
    (fun e => ((Scatter.write (fun _ : Fin n => (0 : ℕ)) (es.map (fun e => (e,u))) e : ℕ) : ℤ)) =
      (Scatter.withWork (fun _ : Fin n => (0 : ℤ)) (es.map (fun e => (e,(u : ℤ))))).1 := by
  rw [Scatter.withWork_value]
  simpa only [List.map_map,Function.comp_def,Nat.cast_zero] using
    Scatter.map_write (fun x : ℕ => (x : ℤ)) (fun _ : Fin n => (0 : ℕ)) (es.map (fun e => (e,u)))

/-- The candidate objective uses at most one cost-times-bottleneck product
per edge in its absolute-magnitude budget. -/
theorem scatter_constant_objective_mass (J : Circulation) (es : List (Fin J.m)) (u C : ℕ)
    (hc : J.CostsBounded C) :
    objectiveScanMass J (Scatter.write (fun _ => 0) (es.map (fun e => (e,u))))
      (List.finRange J.m)≤J.m*(C*u) := by
  have h := objectiveScanMass_le J _ (List.finRange J.m) C u (fun e _ => hc e)
    (fun e _ => scatter_constant_le (fun _ => 0) es u (fun _ => Nat.zero_le u) e)
  simpa only [List.length_finRange] using h

end MinCostFlow.Scaling.Machine
