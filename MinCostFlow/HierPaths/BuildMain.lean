module

public import MinCostFlow.HierPaths.BuildRoot

/-!
# The static construction, in one statement

`static_construction` puts together what the static construction gives, with the host of
`lemma_2` at the root (`buildHyp_root`): the output is a hierarchy (`hier_isValid`), it meets the
bounds of `HierData.Bounds` with `d_j = routePathLen Δ b̂_j L`, `ρ_j = (49 L' + 2) R_j` and `κ_j = R_j`, where `b̂_j` is the
router scale at depth `j`,
(`hier_bounds`), and its work over the depths `j < D` is at most `∑_{j < D} 2^x · F_j(2^b)`
(`buildCost_le`).
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

namespace BuildParams

/-- **The static construction.** -/
theorem static_construction {B : BuildParams} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer B.route routeCost) :
    ∃ C, ∀ {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ},
      IsCorePlayer cfg B.M B.r B.core coreCost →
      ∀ {G : Graph}, G.IsValid → 1 ≤ G.m → ∀ {φ : ℝ}, 0 < φ →
      G.IsConductanceExpanderOn G.verts φ → hostSize G = 2 ^ B.x → ∀ {bh : ℕ → ℕ},
      (∀ j, max 2 (2 / B.rootβ cfg φ j) ≤ (bh j : ℝ)) →
      49 * B.L' + 2 ≤ B.Δ → 1 ≤ B.L → B.x < B.L → B.x < B.L' →
      2 ^ B.x ≤ (NOf B.M B.r) ^ B.r → 49 * B.L' ≤ deltaParam B.M →
      (B.hier (hostGraph ExplicitExpander.explicitGraph G)).IsValid B.x B.b ∧
      (B.hier (hostGraph ExplicitExpander.explicitGraph G)).Bounds B.x B.b
        (fun j => routePathLen B.Δ (bh j) B.L)
        (fun j => (49 * B.L' + 2) * routeCong B.Δ (bh j) B.L)
        (fun j => routeCong B.Δ (bh j) B.L) ∧
      ∀ D, B.buildCost routeCost coreCost (hostGraph ExplicitExpander.explicitGraph G) D ≤
        ∑ j ∈ Finset.range D, 2 ^ B.x * B.unitCost cfg C (bh j) (2 ^ B.b) := by
  obtain ⟨C, hC⟩ := hrouter.cost_bound
  refine ⟨C + 2, fun {cfg coreCost} hcore {G} hG hm {φ} hφ hcond hx {bh} hbh hdeg hL hxL hxL' hsize
    hcd => ?_⟩
  have hyp := buildHyp_root (B := B) (cfg := cfg) hG hm hφ hcond hx hbh hdeg hL hxL hxL' hsize hcd
  exact ⟨hier_isValid hrouter hcore hyp, hier_bounds hrouter hcore hyp,
    fun D => buildCost_le hrouter hC hcore hyp D⟩

end BuildParams

end MinCostFlow.HierPaths
