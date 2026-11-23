module

public import MinCostFlow.Scaling.CapacityLoopBounds
public import MinCostFlow.Scaling.VertexCompression

/-!
# The complete counted capacity-scaling model

Lemma C.9 of Chen et al., arXiv:2203.00671v2, reduces arbitrary capacities to
polynomially bounded ones. This function handles the empty graph directly,
compresses vertices once, and runs the counted capacity loop. Every supplied
solver input has polynomial costs and positive polynomial capacities. This
file proves those input and counter bounds, not final optimality.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- The capacity-scaling model with a one-time isolated-vertex compression. -/
def capacityScalingModel (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) : CallResult (Fin I.m → ℤ) :=
  if I.m = 0 then ⟨fun _ => 0, [], 1⟩
  else
    let r := capacityLoop solve I.compress U
    ⟨r.value.flow, r.calls, I.n + 20 * I.m + 1 + r.work⟩

/-- The complete model has the product-of-padded-logarithms call bound. -/
theorem capacityScalingModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    (capacityScalingModel solve I U).calls.length ≤
      24 * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) := by
  unfold capacityScalingModel
  split
  · simp
  · exact capacityLoop_calls_le_logs solve I.compress U

/-- Every supplied solver input has exactly `2*m` edges. -/
theorem capacityScalingModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    ∀ J ∈ (capacityScalingModel solve I U).calls, J.m = 2 * I.m := by
  unfold capacityScalingModel
  split
  · simp
  · exact capacityLoop_edges solve I.compress U

/-- Every supplied solver input satisfies its own polynomial cost bound. -/
theorem capacityScalingModel_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (capacityScalingModel solve I U).calls, J.CostsBounded (J.m ^ 10) := by
  unfold capacityScalingModel
  split
  · simp
  · exact capacityLoop_costs solve I.compress U hc

/-- Every supplied solver input has positive capacities at most its own
number of edges to power forty, exactly as in the source's solver hypothesis. -/
theorem capacityScalingModel_capacities (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    ∀ J ∈ (capacityScalingModel solve I U).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := by
  unfold capacityScalingModel
  split
  · simp
  · exact capacityLoop_capacities solve I.compress U

/-- The vertex scan occurs once. The rest of the counter has the source's
`m log m log(mU)` form with an explicit coefficient and padded logarithms. -/
theorem capacityScalingModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) (hm : 0 < I.m) :
    (capacityScalingModel solve I U).work ≤
      300000 * I.m * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) + I.n := by
  unfold capacityScalingModel
  rw [ite_eq_right (Nat.ne_of_gt hm)]
  dsimp only
  have hw := capacityLoop_work_le_logs solve I.compress U hm I.endpointLabels_count_le
  change (capacityLoop solve I.compress U).work ≤
    200000 * I.m * (Nat.clog 2 (I.m + 1) + 1) *
      (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) at hw
  have hB : 1 ≤ Nat.clog 2 (I.m + 1) + 1 := Nat.zero_lt_succ _
  have hS : 1 ≤ Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1 := Nat.zero_lt_succ _
  have h1 := Nat.mul_le_mul_left I.m hB
  have h2 := Nat.mul_le_mul_left (I.m * (Nat.clog 2 (I.m + 1) + 1)) hS
  simp only [Nat.mul_one] at h1 h2
  have hp := le_trans h1 h2
  simp only [Nat.mul_assoc] at hw hp ⊢
  omega

end MinCostFlow.Scaling
