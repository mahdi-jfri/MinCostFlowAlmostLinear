module

public import MinCostFlow.ExplicitExpander.Graph
import MinCostFlow.ExplicitExpander.Expansion
import MinCostFlow.ExplicitExpander.Degree

/-!
# The explicit expander: the graph part of Theorem 2.4 of [CGLNPS21]

This file collects the properties of `explicitGraph n` that `Cited.ExplicitExpander` asks for:
it has `n` vertices, its edges join vertices, it has no loops, it has expansion at least `1/12`,
and its degrees are at most `9`. The program that writes it is in `Program.lean`.
-/

public section

namespace MinCostFlow.ExplicitExpander

open MinCostFlow.Cited

/-- The expansion constant `α₀` of the explicit expander. -/
@[expose] noncomputable def alpha0 : ℝ := 1 / 12

/-- **The explicit expander.** For every `n > 1`, `explicitGraph n` is a loopless graph on `n`
vertices with expansion at least `α₀ = 1/12` and degrees at most `9`. -/
theorem explicitGraph_spec (n : ℕ) (hn : 1 < n) :
    (explicitGraph n).n = n ∧ (explicitGraph n).IsValid ∧ (explicitGraph n).IsLoopless ∧
      (explicitGraph n).IsExpansionExpanderOn (explicitGraph n).verts alpha0 ∧
      ∀ v < n, (explicitGraph n).deg v ≤ 9 :=
  ⟨rfl, explicitGraph_isValid n hn.le, explicitGraph_isLoopless n hn.le,
    explicitGraph_expansion n hn.le, fun v _ => explicitGraph_deg_le n hn.le v⟩

end MinCostFlow.ExplicitExpander
