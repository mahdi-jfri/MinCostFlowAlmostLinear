module

public import MinCostFlow.Scaling.CyclePeelFinishCode
public import MinCostFlow.Scaling.SignedAddProgram
public import MinCostFlow.Scaling.BoolTableSetProgram
public import MinCostFlow.Scaling.IndexListConsProgram
import WordRAM.Logic

/-!
# Peeling the stack after a repeated vertex

An empty stack ends the scan. Otherwise add its first edge's cost to the
cycle cost, allocate a node for that edge, and clear its head's path flag
when it differs from the target. The finishing procedure then tests
whether the edge closes the cycle and records the resulting state.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Pass the prepared edge, signed sum, and list pointers to the finishing
procedure and return its traversal heap. -/
def cyclePeelContinue (finish : ℕ) : Stmt :=
  .call 16 finish [.reg 1,.reg 4,.reg 8,.reg 6,.reg 10,.reg 13,.reg 14,.reg 11] ;;
  .ret (.reg 16)

/-- Arguments `[graph,stateBase,heap]`; the current mode is peel. -/
def cyclePeelBody (header add pair flags finish : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .cond (.bin .eq (.reg 3) (.const 0))
    (.call 16 header [.const 3,.const 0,.load (.bin .add (.reg 1) (.const 2)),.const 0,
      .load (.bin .add (.reg 1) (.const 4)),.load (.bin .add (.reg 1) (.const 5)),
      .load (.bin .add (.reg 1) (.const 6)),.const 0,.const 0,.reg 1] ;;
     .ret (.reg 2))
    (.assign 5 (.load (.reg 3)) ;;
     .assign 6 (.load (.bin .add (.reg 3) (.const 1))) ;;
     .assign 7 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 5) (.reg 5))) ;;
     .assign 8 (.load (.reg 7)) ;;
     .assign 9 (.load (.bin .add (.reg 7) (.const 1))) ;;
     .call 10 add [.load (.bin .add (.reg 1) (.const 5)),
       .load (.bin .add (.reg 1) (.const 6)),.load (.bin .add (.reg 7) (.const 3)),
       .load (.bin .add (.reg 7) (.const 4)),.reg 2] ;;
     .call 11 pair [.reg 5,.load (.bin .add (.reg 1) (.const 4)),.reg 10] ;;
     .assign 13 (.load (.reg 2)) ;;
     .assign 14 (.load (.bin .add (.reg 2) (.const 1))) ;;
     .cond (.bin .eq (.reg 9) (.reg 4))
       (cyclePeelContinue finish)
       (.call 15 flags [.bin .add (.reg 1) (.const 9),.reg 9,.const 0] ;;
        cyclePeelContinue finish))

/-- The entry, header writer, signed addition, list cons, Boolean store,
and finishing entry have fixed consecutive addresses. -/
def cyclePeelModule (b : ℕ) : List Stmt :=
  cyclePeelBody (b+1) (b+4) (b+6) (b+7) (b+8) ::
    (cycleHeaderModule (b+1) ++ signedAddModule (b+4) ++ wordPairModule ++
      boolTableSetModule ++ cyclePeelFinishModule (b+8))

/-- Peel dispatch supplies its target vertex to the common step interface. -/
def cyclePeelContract (w : ℕ) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (target : Fin J.n) : Contract :=
  let H := cycleStepContract w J s B C
  { H with pre := fun args mem => H.pre args mem ∧ s.mode=.peel target }

/-- The entry and every callee have no random instruction. -/
theorem cyclePeelModule_noRand (b : ℕ) : ∀ body ∈ cyclePeelModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cyclePeelBody,cyclePeelContinue,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hf
    · rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hp
        · rcases List.mem_append.mp hb with hh | ha
          · exact cycleHeaderModule_noRand _ body hh
          · exact signedAddModule_noRand _ body ha
        · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hp
          subst body
          exact wordPairBody_noRand
      · have he : body=boolTableSetBody := by simpa only [boolTableSetModule,List.mem_singleton] using hb
        subst body
        exact boolTableSetBody_noRand
    · exact cyclePeelFinishModule_noRand _ body hf

end MinCostFlow.Scaling.Machine
