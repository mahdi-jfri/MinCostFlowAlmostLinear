module

public import MinCostFlow.Scaling.BottleneckSearch
public import MinCostFlow.Scaling.CycleExtractionSize
public import MinCostFlow.Scaling.Scatter

/-!
# Counted bottleneck approximation model

The procedure of Lemma C.10 of Chen et al., arXiv:2203.00671v2, searches for
the largest capacity threshold admitting a negative cycle. It extracts a cycle
from the returned unit circulation and sends the threshold amount around that
cycle. This file combines those integer functions and proves their call and
work bounds. The returned magnitude is computed from the actual integer flow
objective. Approximation correctness is a separate mathematical result.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- The integer candidate flow and the nonnegative magnitude computed from its cost. -/
structure ApproximationResult (I : Circulation) where
  flow : Fin I.m → ℤ
  magnitude : ℕ

/-- The source's largest-bottleneck procedure, retaining all bounded-solver
calls and using table writes to construct the candidate integral circulation. -/
def polyApproxModel (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) :
    CallResult (ApproximationResult I) :=
  let search := bottleneckSearch solve I
  match search.value.best with
  | none => ⟨⟨fun _ => 0, 0⟩, search.calls, search.work + 1⟩
  | some (u, f) =>
    let cycle := I.extractCycleModel f
    match cycle.1.result with
    | none => ⟨⟨fun _ => 0, 0⟩, search.calls, search.work + cycle.2 + 1⟩
    | some es =>
      let writes := es.map (fun e => (e, (u : ℤ)))
      let result := Scatter.withWork (fun _ : Fin I.m => (0 : ℤ)) writes
      let cost := I.integerObjective result.1
      ⟨⟨result.1, (-cost).toNat⟩, search.calls,
        search.work + cycle.2 + 5 * I.m + 3 * es.length + result.2 + 8⟩

/-- Cycle extraction and candidate construction make no further solver calls. -/
theorem polyApproxModel_call_trace (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : (polyApproxModel solve I).calls = (bottleneckSearch solve I).calls := by
  unfold polyApproxModel
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- The approximation model uses at most `clog_2(m+1)` solver calls. -/
theorem polyApproxModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    (polyApproxModel solve I).calls.length ≤ Nat.clog 2 (I.m + 1) := by
  rw [polyApproxModel_call_trace]
  exact bottleneckSearch_calls solve I

/-- Every approximation-model call uses exactly the original edge count. -/
theorem polyApproxModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : ∀ J ∈ (polyApproxModel solve I).calls, J.m = I.m := by
  rw [polyApproxModel_call_trace]
  exact bottleneckSearch_edges solve I

/-- Every approximation-model call has positive unit capacities. -/
theorem polyApproxModel_capacities (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    ∀ J ∈ (polyApproxModel solve I).calls, ∀ e, J.capacity e = 1 := by
  rw [polyApproxModel_call_trace]
  exact bottleneckSearch_capacities solve I

/-- Every approximation-model call satisfies the source's polynomial cost bound. -/
theorem polyApproxModel_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (polyApproxModel solve I).calls, J.CostsBounded (J.m ^ 10) := by
  rw [polyApproxModel_call_trace]
  exact bottleneckSearch_costs solve I hc

/-- Cycle extraction and scattering add at most a linear counter beyond the
sorted bottleneck search. This bound uses the returned-list length theorem. -/
theorem polyApproxModel_extra_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    (polyApproxModel solve I).work ≤ (bottleneckSearch solve I).work +
      400 * (I.m + I.n + 1) := by
  unfold polyApproxModel
  dsimp only
  split
  · dsimp only
    omega
  · rename_i u f he
    have hc := I.extractCycleModel_work f
    split
    · dsimp only
      omega
    · rename_i es hes
      have hl := I.extractCycleModel_result_length f es hes
      dsimp only
      rw [Scatter.withWork_work, List.length_map]
      omega

/-- Sorting, binary search, cycle extraction, and flow assembly have an
explicit `O(m log m+n)` model counter. -/
theorem polyApproxModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    (polyApproxModel solve I).work ≤
      120 * (Nat.clog 2 (I.m + 1) + 1) * (I.m + 1) + 400 * (I.m + I.n + 1) := by
  have he := polyApproxModel_extra_work solve I
  have hs := bottleneckSearch_work solve I
  exact le_trans he (Nat.add_le_add_right hs _)

/-- The magnitude is evaluated from the returned integer vector, including
both zero-result branches. -/
theorem polyApproxModel_magnitude (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    (polyApproxModel solve I).value.magnitude =
      (-(I.integerObjective (polyApproxModel solve I).value.flow)).toNat := by
  unfold polyApproxModel
  dsimp only
  split
  · simp [Circulation.integerObjective]
  · split
    · simp [Circulation.integerObjective]
    · rfl

end MinCostFlow.Scaling
