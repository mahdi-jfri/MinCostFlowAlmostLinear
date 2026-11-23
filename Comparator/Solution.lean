module

public import MinCostFlow.Statement.Main
import MinCostFlow.Final.Theorem11Goals

/-!
# Deterministic almost-linear-time minimum-cost flow

This file proves the statement of `Comparator/Challenge.lean`: Theorem 1.1 (page 2) of
*A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow* (arXiv:2309.16629v1). The
proof is `MinCostFlow.Final.DryRun.theorem_1_1_proved` (`MinCostFlow/Final/Theorem11Goals.lean`).

There are no cited-result hypotheses: the library proves every cited result, or the case of it
that the paper uses. Theorem 2.4 of Chuzhoy, Gao, Li, Nanongkai, Peng and Saranurak,
arXiv:1910.08025v2 (the explicit expander, cited as [CGLNPS21] for Theorem 8.4) is
`MinCostFlow.ExplicitExpander.explicitExpander`. Theorem 1 of Abraham and Neiman, SIAM J. Comput.
2019 (the low-stretch spanning tree, cited as [AN19] for Theorem 2.2) is
`MinCostFlow.LowStretch.lowStretchSpanningTree_lsst`. For Corollary 6.1 of [CGLNPS21] (the
expander decomposition, cited for Theorems 8.5 and B.1), the case the paper uses
(`MinCostFlow.ExpanderDecomp.ExpanderDecompositionUsed`) is
`MinCostFlow.ExpanderDecomp.expanderDecompositionUsed_holds`. For Theorem 3.9 of Chuzhoy and
Saranurak, arXiv:2009.08479v1 (decremental expander paths, cited as [CS21] for Theorem 8.6), the
static sparsifier of Theorem 8.1 is proved directly from a deterministic hierarchy of embedded
matchings (`MinCostFlow.HierPaths.hierPathDSExistsFrom` and
`MinCostFlow.HierPaths.theorem_8_1_concrete_unconditional`).
-/

public section

namespace MinCostFlow

/-- **Theorem 1.1** (Min-cost flow, page 2). There is a deterministic algorithm that, given a
graph with `m` edges, integral demands and capacities bounded by `U` in absolute value and
integral costs bounded by `C` in absolute value, computes an exact minimum-cost flow, or reports
that no flow is feasible, in time `O(n) + m^{1+o(1)} log U log C`. -/
theorem theorem_1_1 : MinCostFlowStatement :=
  MinCostFlow.Final.DryRun.theorem_1_1_proved

end MinCostFlow
