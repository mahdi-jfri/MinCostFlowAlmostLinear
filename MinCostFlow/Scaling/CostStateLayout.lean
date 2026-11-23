module

public import MinCostFlow.Scaling.CostLoopModel
public import MinCostFlow.Scaling.SolverOutputLayout
public import MinCostFlow.Scaling.SignedTableLayout
import WordRAM.Memory

/-!
# Cost-scaling state in memory

A cost state keeps an unsigned integral flow, signed potential numerators,
and a natural denominator power. Its three-word header stores the two
array pointers and the power. The arrays lie below the supplied heap
bound. Feasibility and arithmetic bounds are proved separately from this
data representation.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Exact cost-state data in the common flow and signed-table layouts. -/
def CostStateAt {J : Circulation} (mem : ℕ → ℕ) (base bound : ℕ) (s : CostState J) : Prop :=
  ∃ flow pot,ListAt mem base [flow,pot,s.power] ∧ flow+J.m≤bound ∧ pot+2*J.n≤bound ∧
    J.readSolverFlow mem flow=s.flow ∧ SignedTableAt mem pot s.potential

/-- The exact unsigned flow array and signed potential table, with their
three-word header, give the cost-state representation. -/
theorem costStateAt_of_arrays {J : Circulation} {mem : ℕ → ℕ} {base bound flow pot : ℕ} {s : CostState J}
    (hheader : ListAt mem base [flow,pot,s.power]) (hflowEnd : flow+J.m≤bound) (hpotEnd : pot+2*J.n≤bound)
    (hflow : ListAt mem flow (List.ofFn (fun e => (s.flow e).toNat))) (hnonneg : ∀ e,0≤s.flow e)
    (hpot : SignedTableAt mem pot s.potential) : CostStateAt mem base bound s :=
  ⟨flow,pot,hheader,hflowEnd,hpotEnd,solverOutput_read_eq J hnonneg hflow,hpot⟩

/-- Preserving an old prefix preserves both arrays and the cost-state
header when enlarging its heap bound. -/
theorem CostStateAt.of_agree_below {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {s : CostState J} (hat : CostStateAt mem base bound s)
    (hheader : base+3≤bound) (hbound : bound≤bound') (hframe : ∀ x<bound,mem' x=mem x) :
    CostStateAt mem' base bound' s := by
  obtain ⟨flow,pot,hstored,hflowEnd,hpotEnd,hread,hpot⟩ := hat
  refine ⟨flow,pot,hstored.of_agree_below (h₀ := bound) hheader hframe,hflowEnd.trans hbound,
    hpotEnd.trans hbound,?_,hpot.of_agree_below hpotEnd hframe⟩
  funext e
  have h := congrFun hread e
  change (mem' (flow+e.val) : ℤ)=s.flow e
  change (mem (flow+e.val) : ℤ)=s.flow e at h
  rw [hframe _ (by have he := e.isLt; omega)]
  exact h

end MinCostFlow.Scaling.Machine
