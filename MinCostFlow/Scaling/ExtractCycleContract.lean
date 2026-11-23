module

public import MinCostFlow.Scaling.CycleInitialProgram
public import MinCostFlow.Scaling.CycleRunContract
import WordRAM.Logic

/-!
# Complete cycle extraction entry

Initialize the outgoing lists and candidate stack, then run the model's
`6*m+1` rounds. The potential bound proves that this fuel suffices. The
entry returns the full final state, including its optional extracted
cycle, in the shared traversal layout.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,flow,stateHeap]`. -/
def extractCycleBody (initial run : ℕ) : Stmt :=
  .call 3 initial [.reg 0,.reg 1,.reg 2] ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.bin .mul (.const 6) (.reg 4)) (.const 1)) ;;
  .call 6 run [.reg 0,.reg 2,.reg 5,.reg 3] ;;
  .ret (.reg 6)

/-- The initializer and bounded traversal follow the extraction entry. -/
def extractCycleModule (b : ℕ) : List Stmt :=
  let run := b+1+(cycleInitialModule (b+1)).length
  extractCycleBody (b+1) run :: (cycleInitialModule (b+1) ++ cycleRunModule run)

/-- Exact full-state model extraction with a linear fresh-space reserve
and one-word bounds for every accumulated cycle cost. -/
def extractCycleContract (w : ℕ) (J : Circulation) (flow : Fin J.m → ℤ) (C : ℕ) : Contract where
  pre args mem := ∃ a flowPtr base,args=[a,flowPtr,base] ∧
    ListAt mem a J.solverWords ∧ ListAt mem flowPtr (List.ofFn (fun e => (flow e).toNat)) ∧
    a+J.solverWords.length≤base ∧ flowPtr+J.m≤base ∧
    (∀ e,0≤flow e ∧ (flow e).toNat<2^w) ∧ J.CostsBounded C ∧
    ZeroFrom mem base ∧ base+10+3*J.n+28*J.m+8<2^w ∧ (6*J.m+2)*C<2^w ∧ 9<2^w
  post args mem ret mem' := cycleNodes J.n (heapArg args)≤ret ∧
    ret≤cycleNodes J.n (heapArg args)+28*J.m+4 ∧
    CycleStateAt mem' (heapArg args) ret (J.extractCycleModel flow).1 ∧
    ZeroFrom mem' ret ∧ (∀ x<heapArg args,mem' x=mem x) ∧
    ∀ i<9,mem' (heapArg args+i)<2^w
  cost _ _ := 7600*J.m+2000

/-- The extraction entry and all initialization and traversal code have
no random instruction. -/
theorem extractCycleModule_noRand (b : ℕ) : ∀ body ∈ extractCycleModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [extractCycleBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hi | hr
    · exact cycleInitialModule_noRand _ body hi
    · exact cycleRunModule_noRand _ body hr

end MinCostFlow.Scaling.Machine
