module

public import MinCostFlow.Final.Theorem11Bundle
public import MinCostFlow.NarrowTop.Theorem

/-!
# Theorem 1.1 from the narrow-word top theorem (`Theorem11Goals`)

Re-exports the proved solver bundle from `Final/Theorem11Bundle.lean` and proves
`theorem_1_1_proved : MinCostFlowStatement` with no hypothesis from
`NarrowTop.narrowStatement_proved`. `Comparator/Challenge.lean` proves `MinCostFlow.theorem_1_1`
from this theorem.
-/

public section

namespace MinCostFlow.Final.DryRun

/-- **Theorem 1.1** (Min-cost flow, page 2 of arXiv:2309.16629v1), with no hypothesis. Proved from
the narrow-word top theorem `NarrowTop.narrowStatement_proved`, whose encoding and answer predicate
agree with `MinCostFlowStatement` by `rfl`. `Comparator/Challenge.lean` states the theorem as
`MinCostFlow.theorem_1_1` and proves it from this one. -/
theorem theorem_1_1_proved : MinCostFlowStatement :=
  NarrowTop.minCostFlowStatement_of_narrow NarrowTop.narrowStatement_proved

end MinCostFlow.Final.DryRun

end
