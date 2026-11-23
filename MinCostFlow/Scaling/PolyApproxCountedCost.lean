module

public import MinCostFlow.Scaling.PolyApproxContract
import MinCostFlow.Scaling.ApproximationWorkLower
import MinCostFlow.Scaling.BottleneckGuestBounds
import Mathlib.Tactic.Ring

/-!
# Charging approximation execution to its actual counters

Every active threshold query reserves linear work. That pays for its
logarithmic canonical guest setup. The remaining scan and scatter costs
are paid by the approximation's own work counter. This gives the direct
call-plus-work bound needed when composing the outer scaling loops.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem guest_overhead (m reg guest : ℕ) (hg : 40*guest≤9000*(m+1)) :
    40*guest+reg≤10000*(reg+1)*(m+1) := by
  have hr : reg≤reg*(m+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left reg (show 1≤m+1 by omega)
  have htop : 10000*(reg+1)*(m+1)=10000*(reg*(m+1))+10000*(m+1) := by ring
  rw [htop]
  omega

private theorem rest_cost {m sw mw : ℕ} (hs : sw+1≤mw) (hm : m+1≤mw) :
    200*sw+1500+9000*(m+1)+100≤10800*mw := by omega

private theorem finish_cost {base charge rest weight : ℕ}
    (hc : charge≤10000*weight) (hr : rest≤10800*weight) :
    base+charge+rest≤base+30000*weight := by omega

private theorem counted_cost (calls solveCost guest reg searchWork modelWork m : ℕ)
    (hwork : calls*(m+1)≤searchWork) (hs : searchWork+1≤modelWork) (hm : m+1≤modelWork)
    (hg : 40*guest+reg≤10000*(reg+1)*(m+1)) :
    calls*(solveCost+40*guest+reg)+200*searchWork+1500+9000*(m+1)+100≤
      calls*solveCost+30000*(reg+1)*modelWork := by
  have hcharge : calls*(40*guest+reg)≤10000*(reg+1)*modelWork := by
    calc
      _ ≤ calls*(10000*(reg+1)*(m+1)) := Nat.mul_le_mul_left calls hg
      _ = 10000*(reg+1)*(calls*(m+1)) := by ring
      _ ≤ 10000*(reg+1)*modelWork := Nat.mul_le_mul_left _ (hwork.trans (by omega))
  have hrest := rest_cost hs hm
  have hweight : modelWork≤(reg+1)*modelWork := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right modelWork (show 1≤reg+1 by omega)
  have hrest' : 200*searchWork+1500+9000*(m+1)+100≤10800*(reg+1)*modelWork :=
    hrest.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10800 hweight)
  have heq : calls*(solveCost+40*guest+reg)=calls*solveCost+calls*(40*guest+reg) := by ring
  rw [heq]
  have hcharge' : calls*(40*guest+reg)≤10000*((reg+1)*modelWork) := by
    simpa only [Nat.mul_assoc] using hcharge
  have hfinal := finish_cost (base := calls*solveCost) hcharge'
    (by simpa only [Nat.mul_assoc] using hrest')
  simpa only [Nat.add_assoc,Nat.mul_assoc] using hfinal

/-- The complete approximation execution is bounded directly by its actual
solver-call count and work counter, with an explicit coefficient. -/
theorem polyApprox_cost_counted (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    let r := polyApproxModel (canonicalSolver solver entry T hproc) J
    (polyApproxContract w solver entry T hproc J C U).cost args mem≤
      r.calls.length*((solver.regBound+6)*T (J.n+1) J.m)+30000*(solver.regBound+1)*r.work := by
  let solve := canonicalSolver solver entry T hproc
  let G := bottleneckGuestBound J (sortCapacities (List.ofFn J.capacity)).1
  have hG := bottleneckGuestBound_le J (sortCapacities (List.ofFn J.capacity)).1 hn hc
  have hlog : Nat.clog 2 (J.m+2)≤J.m+2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hg : 40*G≤9000*(J.m+1) := by change 40*bottleneckGuestBound J _≤_; omega
  have hwork := bottleneckSearch_calls_mul_le_work solve J
  have hmodel := polyApproxModel_work_lower solve J
  have hbound := counted_cost (bottleneckSearch solve J).calls.length
    ((solver.regBound+6)*T (J.n+1) J.m) G solver.regBound
    (bottleneckSearch solve J).work (polyApproxModel solve J).work J.m
    hwork hmodel.1 hmodel.2 (guest_overhead J.m solver.regBound G hg)
  change (bottleneckSearch solve J).calls.length*
    ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound)+
    200*(bottleneckSearch solve J).work+1500+9000*(J.m+1)+100≤_
  simpa only [polyApproxModel_call_trace] using hbound

end MinCostFlow.Scaling.Machine
