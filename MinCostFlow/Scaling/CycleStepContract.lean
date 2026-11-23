module

public import MinCostFlow.Scaling.CycleStateLayout
public import MinCostFlow.Scaling.CycleMachineBounds
public import MinCostFlow.Scaling.SolverContract

/-!
# Machine interface for a single cycle traversal step

The graph lies before the fixed traversal arrays. Immutable list nodes
occupy the remaining old heap prefix. One walk push uses two fresh cells,
and peeling can additionally allocate the signed sum. Thus four cells
suffice for every step. The arithmetic budget covers one cost addition.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Exact cycle-step state, four-cell fresh reserve, and complete frames
outside the fixed header/vertex arrays. Header word bounds are maintained. -/
def cycleStepContract (w : ℕ) (J : Circulation) (s : Circulation.CycleState J) (B C : ℕ) : Contract where
  pre args mem := ∃ a base heap,args=[a,base,heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length≤base ∧ CycleStateAt mem base heap s ∧ cycleNodes J.n base≤heap ∧
    (∀ i<9,mem (base+i)<2^w) ∧ s.cycleCost.natAbs≤B ∧ J.CostsBounded C ∧
    B+C<2^w ∧ s.potential+1<2^w ∧ ZeroFrom mem heap ∧ heap+4<2^w ∧ 9<2^w
  post args mem ret mem' := heapArg args≤ret ∧ ret≤heapArg args+4 ∧
    CycleStateAt mem' (args.getD 1 0) ret s.step ∧ ZeroFrom mem' ret ∧
    (∀ x<heapArg args,x<args.getD 1 0 ∨ cycleNodes J.n (args.getD 1 0)≤x → mem' x=mem x) ∧
    ∀ i<9,mem' (args.getD 1 0+i)<2^w
  cost _ _ := 1000

/-- The choose-mode implementation uses the same interface and only adds
the model's current mode as a dispatch condition. -/
def cycleChooseContract (w : ℕ) (J : Circulation) (s : Circulation.CycleState J) (B C : ℕ) : Contract :=
  let H := cycleStepContract w J s B C
  { H with pre := fun args mem => H.pre args mem ∧ s.mode=.choose }

end MinCostFlow.Scaling.Machine
