module

public import MinCostFlow.Scaling.CycleStepProgram
import WordRAM.Logic

/-!
# Interface for the bounded cycle traversal

Each unfinished round performs one step and recurses with one less unit
of fuel. Done states return immediately, as in the model. The arithmetic
budget permits one edge-cost increase per remaining round; the heap
reserve permits four cells per round and one additional step reserve.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,stateBase,fuel,heap]`. -/
def cycleRunBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.assign 4 (.load (.reg 1)) ;;
     .cond (.bin .eq (.reg 4) (.const 3)) (.ret (.reg 3))
       (.call 5 step [.reg 0,.reg 1,.reg 3] ;;
        .call 6 self [.reg 0,.reg 1,.bin .sub (.reg 2) (.const 1),.reg 5] ;;
        .ret (.reg 6)))

/-- The recursive entry followed by all traversal modes. -/
def cycleRunModule (b : ℕ) : List Stmt :=
  cycleRunBody b (b+1) :: cycleStepModule (b+1)

/-- A finite traversal with exact model output and linear time and space. -/
def cycleRunContract (w : ℕ) (J : Circulation) (s : Circulation.CycleState J)
    (B C fuel : ℕ) : Contract where
  pre args mem := ∃ a base heap,args=[a,base,fuel,heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length≤base ∧ CycleStateAt mem base heap s ∧ cycleNodes J.n base≤heap ∧
    (∀ i<9,mem (base+i)<2^w) ∧ s.cycleCost.natAbs≤B ∧ J.CostsBounded C ∧
    B+(fuel+1)*C<2^w ∧ s.potential+1<2^w ∧ ZeroFrom mem heap ∧
    heap+4*fuel+4<2^w ∧ fuel<2^w ∧ 9<2^w
  post args mem ret mem' := heapArg args≤ret ∧ ret≤heapArg args+4*fuel ∧
    CycleStateAt mem' (args.getD 1 0) ret (Circulation.CycleState.run fuel s).1 ∧
    ZeroFrom mem' ret ∧
    (∀ x<heapArg args,x<args.getD 1 0 ∨ cycleNodes J.n (args.getD 1 0)≤x → mem' x=mem x) ∧
    ∀ i<9,mem' (args.getD 1 0+i)<2^w
  cost _ _ := 1200*fuel+20

/-- The bounded traversal and every mode entry are deterministic. -/
theorem cycleRunModule_noRand (b : ℕ) : ∀ body ∈ cycleRunModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cycleRunBody,Stmt.NoRand,and_self]
  · exact cycleStepModule_noRand _ body hb

end MinCostFlow.Scaling.Machine
