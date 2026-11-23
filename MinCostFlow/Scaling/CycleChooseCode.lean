module

public import MinCostFlow.Scaling.CycleStepContract
public import MinCostFlow.Scaling.CycleHeaderProgram
public import MinCostFlow.Scaling.BoolTableSetProgram
import WordRAM.Logic

/-!
# Code for choosing the cycle traversal's next start

An empty candidate list completes the scan. Otherwise pop its first edge
and inspect the outgoing list at its tail. Empty outgoing lists are skipped.
A nonempty list starts a walk and marks its vertex. The shared header
writer records exactly the model's fields in each branch.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The supplied nine header fields are followed by the existing state
address. The traversal heap is unchanged. -/
def cycleChooseWrite (header : ℕ) (fields : List Expr) : Stmt :=
  .call 12 header (fields++[.reg 1]) ;; .ret (.reg 2)

/-- Arguments `[graph,stateBase,heap]`; the state is in choose mode. -/
def cycleChooseBody (header flags : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .cond (.bin .eq (.reg 3) (.const 0))
    (cycleChooseWrite header [.const 3,.const 0,.const 0,
      .load (.bin .add (.reg 1) (.const 3)),.load (.bin .add (.reg 1) (.const 4)),
      .load (.bin .add (.reg 1) (.const 5)),.load (.bin .add (.reg 1) (.const 6)),.const 0,.const 0])
    (.assign 4 (.load (.reg 3)) ;;
     .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
     .assign 6 (.load (.reg 0)) ;;
     .assign 7 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 5) (.reg 4))) ;;
     .assign 8 (.load (.reg 7)) ;;
     .assign 9 (.bin .add (.bin .add (.reg 1) (.const 9)) (.reg 6)) ;;
     .assign 10 (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 8))) ;;
     .cond (.bin .eq (.load (.reg 10)) (.const 0))
       (cycleChooseWrite header [.const 0,.const 0,.reg 5,.const 0,
         .load (.bin .add (.reg 1) (.const 4)),.load (.bin .add (.reg 1) (.const 5)),
         .load (.bin .add (.reg 1) (.const 6)),.load (.bin .add (.reg 1) (.const 7)),
         .load (.bin .add (.reg 1) (.const 8))])
       (.call 11 flags [.bin .add (.reg 1) (.const 9),.reg 8,.const 1] ;;
        cycleChooseWrite header [.const 1,.reg 8,.reg 5,.const 0,.const 0,.const 0,.const 0,
          .load (.bin .add (.reg 1) (.const 7)),.load (.bin .add (.reg 1) (.const 8))]))

/-- Choose-mode code followed by its exact header and Boolean stores. -/
def cycleChooseModule (b : ℕ) : List Stmt :=
  cycleChooseBody (b+1) (b+4) :: (cycleHeaderModule (b+1) ++ boolTableSetModule)

/-- Every choose-mode instruction is deterministic. -/
theorem cycleChooseModule_noRand (b : ℕ) : ∀ body ∈ cycleChooseModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cycleChooseBody,cycleChooseWrite,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hh | hf
    · exact cycleHeaderModule_noRand _ body hh
    · have he : body=boolTableSetBody := by simpa only [boolTableSetModule,List.mem_singleton] using hf
      subst body
      exact boolTableSetBody_noRand

end MinCostFlow.Scaling.Machine
