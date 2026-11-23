module

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Adding the complete iteration's amortized charges

Detect/refresh and the checked continuation retain the same concrete
intermediate potential. Cancel it, count the outer call and sequence,
and combine their linear reported-size rates. The resulting constant
covers rejection too, since its continuation is shorter.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The two actual component charges and outer overhead give one charge
linear in one plus the report size, with no extra graph-size factor. -/
theorem detectChecked_cost_sum {n rate length gradient L first tail old middle final : ℕ}
    (hfirst : first+middle≤(n+1)*(2*rate+length+gradient+1534*L+4200)+old)
    (htail : tail+final≤n*(164*L+680)+rate*(1+2*n)+middle+1050) :
    first+tail+22+final≤(n+1)*(4*rate+length+gradient+1698*L+5400)+old := by
  have hh : first+tail+22+final≤
      (n+1)*(2*rate+length+gradient+1534*L+4200)+n*(164*L+680)+rate*(1+2*n)+old+1072 := by omega
  calc
    _≤(n+1)*(2*rate+length+gradient+1534*L+4200)+n*(164*L+680)+rate*(1+2*n)+old+1072 := hh
    _≤((n+1)*(2*rate+length+gradient+1534*L+4200)+n*(164*L+680)+rate*(1+2*n)+old+1072)+
        (520*n+128+rate+164*L) := Nat.le_add_right _ _
    _=_ := by ring

end MinCostFlow.IPM.Machine
