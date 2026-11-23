module

public import MinCostFlow.Scaling.ApproximationFinishContract
import MinCostFlow.Scaling.ApproximationFinishNoneProgram
import MinCostFlow.Scaling.ApproximationFinishSomeProgram

/-!
# Completing every bottleneck search outcome

Split on the exact search model's retained result. The proved branches
return zero after an unsuccessful search, or extract and scatter a cycle
from the retained unit flow. Together they compute exactly the full
approximation result after the search has finished.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every represented exact search result is completed into the exact
approximation model value at cost at most `9000*(m+1)`. -/
theorem approximationFinish_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ}
    {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hp : p.HasAt b (approximationFinishModule b)) (J : Circulation) (C U : ℕ)
    (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (approximationFinishContract w solver entry T hproc J C U) := by
  cases hbest : (bottleneckSearch (canonicalSolver solver entry T hproc) J).value.best with
  | none => exact approximationFinish_none_meetsContract hproc hp J C U hbest
  | some best =>
    obtain ⟨u,flow⟩ := best
    exact approximationFinish_some_meetsContract hproc hp J C U hc u flow hbest

end MinCostFlow.Scaling.Machine
