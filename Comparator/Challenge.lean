module

public import MinCostFlow.Statement.Main

/-!
# Deterministic almost-linear-time minimum-cost flow: the statement to be proved

`MinCostFlow.theorem_1_1` is Theorem 1.1 (page 2) of J. van den Brand, L. Chen, R. Kyng,
Y. P. Liu, R. Peng, M. Probst Gutenberg, S. Sachdeva and A. Sidford, *A Deterministic
Almost-Linear Time Algorithm for Minimum-Cost Flow* (arXiv:2309.16629v1). Its conclusion,
`MinCostFlowStatement`, is defined in `MinCostFlow/Statement/Main.lean`, over the problem of
`MinCostFlow/Statement/Problem.lean` and the machine of `WordRAM/Model.lean`.

`Comparator/Solution.lean` proves the theorem.
-/

public section

namespace MinCostFlow

/-- **Theorem 1.1** (Min-cost flow, page 2). There is a deterministic algorithm that, given a
graph with `m` edges, integral demands and capacities bounded by `U` in absolute value and
integral costs bounded by `C` in absolute value, computes an exact minimum-cost flow, or reports
that no flow is feasible, in time `O(n) + m^{1+o(1)} log U log C`. -/
theorem theorem_1_1 : MinCostFlowStatement :=
  sorry

end MinCostFlow
