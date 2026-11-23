module

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Aggregating budgeted-iteration amortized charges

Add the actual Detect/refresh charge and either credited budget branch.
The same concrete intermediate potential cancels. The result has one
plus the report-size factor, with no extra edge-count factor.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The actual component charges plus fifty prefix/guard operations fit
one linear reported-size rate, retaining the final concrete credit. -/
theorem budgetedIteration_cost_sum {n rate lc gc L first tail old middle final : ℕ}
    (hfirst : first+middle≤(n+1)*(2*rate+lc+gc+1534*L+4200)+old)
    (htail : tail+final≤n*(164*L+680)+rate*(1+2*n)+middle+1092) :
    first+tail+50+final≤(n+1)*(4*rate+lc+gc+1698*L+6000)+old := by
  have heq : (n+1)*(4*rate+lc+gc+1698*L+6000)=
      (n+1)*(2*rate+lc+gc+1534*L+4200)+n*(164*L+680)+rate*(1+2*n)+1092+50+
        (1120*n+658+rate+164*L) := by ring
  rw [heq]
  omega

end MinCostFlow.IPM.Machine
