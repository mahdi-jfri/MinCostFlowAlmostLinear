module

public import MinCostFlow.Scaling.CycleStepContract
public import MinCostFlow.Scaling.CycleHeaderProgram
import WordRAM.Logic

/-!
# Recording one peeled edge in the cycle traversal

After preparing the stack tail, extended cycle list, signed sum, and path
flag, compare the peeled edge's tail with the target. A closed negative
part completes the scan with that exact list. A closed nonnegative part
is discarded and walking resumes at the target. Otherwise peeling
continues. This procedure performs the header update for these cases.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Write a prepared header and return the unchanged traversal heap. -/
def cyclePeelFinishWrite (header : ℕ) (fields : List Expr) : Stmt :=
  .call 8 header (fields++[.reg 0]) ;; .ret (.reg 7)

/-- Arguments `[state,target,edgeTail,stackTail,cycleList,costSign,costMagnitude,heap]`. -/
def cyclePeelFinishBody (header : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.reg 1))
    (.cond (.bin .eq (.reg 5) (.const 1))
      (cyclePeelFinishWrite header [.const 3,.const 0,.load (.bin .add (.reg 0) (.const 2)),
        .reg 3,.reg 4,.reg 5,.reg 6,.const 1,.reg 4])
      (cyclePeelFinishWrite header [.const 1,.reg 1,.load (.bin .add (.reg 0) (.const 2)),
        .reg 3,.const 0,.const 0,.const 0,.load (.bin .add (.reg 0) (.const 7)),
        .load (.bin .add (.reg 0) (.const 8))]))
    (cyclePeelFinishWrite header [.const 2,.reg 1,.load (.bin .add (.reg 0) (.const 2)),
      .reg 3,.reg 4,.reg 5,.reg 6,.load (.bin .add (.reg 0) (.const 7)),
      .load (.bin .add (.reg 0) (.const 8))])

/-- The finishing entry and the shared exact header writer. -/
def cyclePeelFinishModule (b : ℕ) : List Stmt :=
  cyclePeelFinishBody (b+1) :: cycleHeaderModule (b+1)

/-- Prepared pointers and signed sum are represented data, before the
header is changed. A cleared path flag is already false when its vertex
differs from the peeling target. -/
def cyclePeelFinishContract (w : ℕ) (J : Circulation) (s : Circulation.CycleState J)
    (target : Fin J.n) (e : Fin J.m) (rest : List (Fin J.m)) : Contract where
  pre args mem := ∃ base tail cycle heap,args=[base,target.val,(J.tail e).val,tail,cycle,
      if s.cycleCost+J.cost e<0 then 1 else 0,(s.cycleCost+J.cost e).natAbs,heap] ∧
    CycleStateAt mem base heap s ∧ IndexListAt mem (cycleNodes J.n base) heap tail rest ∧
    IndexListAt mem (cycleNodes J.n base) heap cycle (e::s.cycleEdges) ∧
    s.mode=.peel target ∧ s.stack=e::rest ∧ (J.head e=target ∨ s.onPath (J.head e)=false) ∧
    cycleNodes J.n base≤heap ∧ (∀ i<9,mem (base+i)<2^w) ∧ ZeroFrom mem heap ∧ heap<2^w ∧ 9<2^w
  post args mem ret mem' := ret=heapArg args ∧ CycleStateAt mem' (args.getD 0 0) ret s.step ∧
    ZeroFrom mem' ret ∧ (∀ x,x<args.getD 0 0 ∨ args.getD 0 0+9≤x → mem' x=mem x) ∧
    ∀ i<9,mem' (args.getD 0 0+i)<2^w
  cost _ _ := 600

/-- Every finishing branch has no random instruction. -/
theorem cyclePeelFinishModule_noRand (b : ℕ) : ∀ body ∈ cyclePeelFinishModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cyclePeelFinishBody,cyclePeelFinishWrite,Stmt.NoRand,and_self]
  · exact cycleHeaderModule_noRand _ body hb

end MinCostFlow.Scaling.Machine
