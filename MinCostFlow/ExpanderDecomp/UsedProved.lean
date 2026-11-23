module

public import MinCostFlow.ExpanderDecomp.UsedFromRouter
public import MinCostFlow.ExpanderDecomp.RouteProgEntry
public import MinCostFlow.Expander.Section8Static

/-!
# The expander decomposition that the paper uses, proved (`UsedProved`)

`ExpanderDecompositionUsed` (`Statement.lean`) is the case of the cited expander decomposition
(`Cited.ExpanderDecomposition`, Corollary 6.1 of arXiv:1910.08025v2) that the paper uses: the
parameters `a = 1`, `b = 200` and `r = rOf m`. The program of `UsedFromRouter.lean` computes it from
any router module, and `RouteProgEntry.lean` gives one, `routeOrCutRouterModule`. So the used case
holds with no hypothesis.
-/

public section

namespace MinCostFlow.ExpanderDecomp

/-- **The used expander decomposition holds**: the program `assembledDecompProgOfRouter` with the
router `routeOrCutRouterModule` computes it. -/
theorem expanderDecompositionUsed_holds : ExpanderDecompositionUsed :=
  expanderDecompositionUsed_of_router routeOrCutRouterModule

/-- **Concrete Static Sparsifier (Theorem 8.1, page 39)** with only the cited decremental expander
paths as a hypothesis: `Expander.theorem_8_1_concrete_both` at the proved
`expanderDecompositionUsed_holds`, keeping its first part, as `Expander.theorem_8_1_concrete`
does. -/
theorem theorem_8_1_concrete_of_paths (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) := by
  obtain ⟨sparsify, _, params, _, C_γ, K_s, K_t, _, h1, h2, h3, h4, _, h6, _⟩ :=
    Expander.theorem_8_1_concrete_both expanderDecompositionUsed_holds hPaths
  exact ⟨sparsify, params, C_γ, K_s, K_t, h1, h2, h3, h4, h6⟩

end MinCostFlow.ExpanderDecomp
