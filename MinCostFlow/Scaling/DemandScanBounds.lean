module

public import MinCostFlow.Scaling.DemandScan

/-!
# Word bounds during the lower-capacity demand scan

Each input edge subtracts its lower capacity at one vertex and adds it at
another. If current demand magnitudes are at most `B` and the lower capacity
has magnitude at most `L`, both sequential additions use magnitude sums at
most `B+2*L`. The resulting table also has this bound. These integer bounds
supply the local preconditions of the demand-step machine procedure.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- One signed table update increases any magnitude by at most the magnitude
of its contribution. -/
theorem update_add_natAbs_le {n : ℕ} (s : Fin n → ℤ) (v u : Fin n) (z : ℤ) :
    (Function.update s v (s v + z) u).natAbs ≤ (s u).natAbs + z.natAbs := by
  by_cases huv : u = v
  · subst u
    rw [Function.update_self]
    exact Int.natAbs_add_le _ _
  · rw [Function.update_of_ne huv]
    omega

/-- The magnitude sum for the second update includes the first write,
including when both endpoints are the same vertex. -/
theorem demandStep_head_bound (I : Instance) (hv : I.IsValid) (s : Fin I.n → ℤ)
    (e : Fin I.m) (B L : ℕ) (hs : ∀ v, (s v).natAbs ≤ B)
    (hl : (I.edge e).lower.natAbs ≤ L) :
    ((Function.update s ((FlowReduction.shiftedGraph I hv).tail e)
      (s ((FlowReduction.shiftedGraph I hv).tail e) - (I.edge e).lower))
        ((FlowReduction.shiftedGraph I hv).head e)).natAbs + (I.edge e).lower.natAbs ≤ B + 2 * L := by
  rw [sub_eq_add_neg]
  have hh := update_add_natAbs_le s ((FlowReduction.shiftedGraph I hv).tail e)
    ((FlowReduction.shiftedGraph I hv).head e) (-(I.edge e).lower)
  rw [Int.natAbs_neg] at hh
  have hs' := hs ((FlowReduction.shiftedGraph I hv).head e)
  omega

/-- After both endpoint writes, every demand magnitude is at most `B+2*L`. -/
theorem demandStep_natAbs_le (I : Instance) (hv : I.IsValid) (s : Fin I.n → ℤ)
    (e : Fin I.m) (B L : ℕ) (hs : ∀ v, (s v).natAbs ≤ B)
    (hl : (I.edge e).lower.natAbs ≤ L) :
    ∀ v, (FlowReduction.demandStep I hv s e v).natAbs ≤ B + 2 * L := by
  intro v
  let tail := (FlowReduction.shiftedGraph I hv).tail e
  let head := (FlowReduction.shiftedGraph I hv).head e
  let s' := Function.update s tail (s tail + -(I.edge e).lower)
  have ht := update_add_natAbs_le s tail v (-(I.edge e).lower)
  have hh := update_add_natAbs_le s' head v (I.edge e).lower
  rw [Int.natAbs_neg] at ht
  have hs' := hs v
  change (Function.update s' head (s' head + (I.edge e).lower) v).natAbs ≤ _
  change (s' v).natAbs ≤ (s v).natAbs + (I.edge e).lower.natAbs at ht
  omega

end MinCostFlow.Scaling.Machine
