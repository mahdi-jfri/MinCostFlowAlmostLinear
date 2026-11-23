module

public import MinCostFlow.Scaling.CycleStepContract
public import MinCostFlow.Scaling.CycleHeaderProgram
public import MinCostFlow.Scaling.BoolTableSetProgram
public import MinCostFlow.Scaling.AdjacencySetProgram
public import MinCostFlow.Scaling.IndexListConsProgram
import WordRAM.Logic

/-!
# Code for walking an unused cycle-support edge

An exhausted outgoing list returns to choosing a start and clears the
current path flag. Otherwise remove its first edge, push that edge onto
the stack, and inspect its head's flag. A repeated vertex begins peeling.
A new vertex is marked and the walk continues there.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Write the supplied header and return the supplied traversal heap. -/
def cycleWalkWrite (header : ℕ) (fields : List Expr) (heap : Expr) : Stmt :=
  .call 18 header (fields++[.reg 1]) ;; .ret heap

/-- Arguments `[graph,stateBase,heap]`; the current mode is walk. -/
def cycleWalkBody (header flags pair : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 1) (.const 9)) (.reg 3)) ;;
  .assign 6 (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 4))) ;;
  .assign 7 (.load (.reg 6)) ;;
  .cond (.bin .eq (.reg 7) (.const 0))
    (.call 17 flags [.bin .add (.reg 1) (.const 9),.reg 4,.const 0] ;;
     cycleWalkWrite header [.const 0,.const 0,.load (.bin .add (.reg 1) (.const 2)),.const 0,
       .load (.bin .add (.reg 1) (.const 4)),.load (.bin .add (.reg 1) (.const 5)),
       .load (.bin .add (.reg 1) (.const 6)),.load (.bin .add (.reg 1) (.const 7)),
       .load (.bin .add (.reg 1) (.const 8))] (.reg 2))
    (.assign 8 (.load (.reg 7)) ;;
     .assign 9 (.load (.bin .add (.reg 7) (.const 1))) ;;
     .assign 10 (.load (.bin .add (.reg 6) (.const 1))) ;;
     .assign 11 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 5) (.reg 8))) ;;
     .assign 12 (.load (.bin .add (.reg 11) (.const 1))) ;;
     .assign 13 (.load (.bin .add (.bin .add (.reg 1) (.const 9)) (.reg 12))) ;;
     .call 14 pair [.reg 9,.bin .sub (.reg 10) (.const 1),.reg 6] ;;
     .call 15 pair [.reg 8,.load (.bin .add (.reg 1) (.const 3)),.reg 2] ;;
     .cond (.bin .eq (.reg 13) (.const 1))
       (cycleWalkWrite header [.const 2,.reg 12,.load (.bin .add (.reg 1) (.const 2)),.reg 2,
         .const 0,.const 0,.const 0,.load (.bin .add (.reg 1) (.const 7)),
         .load (.bin .add (.reg 1) (.const 8))] (.reg 15))
       (.call 17 flags [.bin .add (.reg 1) (.const 9),.reg 12,.const 1] ;;
        cycleWalkWrite header [.const 1,.reg 12,.load (.bin .add (.reg 1) (.const 2)),.reg 2,
          .load (.bin .add (.reg 1) (.const 4)),.load (.bin .add (.reg 1) (.const 5)),
          .load (.bin .add (.reg 1) (.const 6)),.load (.bin .add (.reg 1) (.const 7)),
          .load (.bin .add (.reg 1) (.const 8))] (.reg 15)))

/-- The walk code shares the same pair body for an in-place outgoing-tail
store and fresh immutable stack cons allocation. -/
def cycleWalkModule (b : ℕ) : List Stmt :=
  cycleWalkBody (b+1) (b+4) (b+5) :: (cycleHeaderModule (b+1) ++ boolTableSetModule ++ wordPairModule)

/-- Walk dispatch supplies its current model vertex to the common step interface. -/
def cycleWalkContract (w : ℕ) (J : Circulation) (s : Circulation.CycleState J) (B C : ℕ) (v : Fin J.n) : Contract :=
  let H := cycleStepContract w J s B C
  { H with pre := fun args mem => H.pre args mem ∧ s.mode=.walk v }

/-- All walk branches and callees have no random instruction. -/
theorem cycleWalkModule_noRand (b : ℕ) : ∀ body ∈ cycleWalkModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cycleWalkBody,cycleWalkWrite,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hp
    · rcases List.mem_append.mp hb with hh | hf
      · exact cycleHeaderModule_noRand _ body hh
      · have he : body=boolTableSetBody := by simpa only [boolTableSetModule,List.mem_singleton] using hf
        subst body
        exact boolTableSetBody_noRand
    · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hp
      subst body
      exact wordPairBody_noRand

end MinCostFlow.Scaling.Machine
