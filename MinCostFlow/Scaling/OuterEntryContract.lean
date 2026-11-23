module

public import MinCostFlow.Scaling.ArbitraryDemandContract
public import MinCostFlow.Scaling.InputBoundsProgram
public import MinCostFlow.Scaling.OutputCopyProgram

/-!
# The whole scaling program's entry and contract

Procedure zero receives only the length of the required input encoding.
It computes the exact input bounds, calls arbitrary-demand scaling, reads
the answer pointer and length from its internal header, copies that many
words to address zero, and returns the length. Its program depends only
on the supplied circulation solver, not on an input instance or a proof.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The entry reads only the original input and the computed pair of bounds. -/
def outerEntryBody (bounds solve copy : ℕ) : Stmt :=
  .call 1 bounds [.const 0,.reg 0] ;;
  .call 2 solve [.const 0,.load (.reg 0),.load (.bin .add (.reg 0) (.const 1)),.reg 1] ;;
  .assign 3 (.load (.bin .sub (.reg 2) (.const 2))) ;;
  .assign 4 (.load (.bin .sub (.reg 2) (.const 1))) ;;
  .call 5 copy [.reg 3,.const 0,.reg 4] ;;
  .ret (.reg 4)

/-- The original-input entry, its bound scans, arbitrary-demand scaling,
and final copy procedure occupy consecutive slots. -/
def outerEntryModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let solve := b+1+(inputBoundsModule (b+1)).length
  let copy := solve+(arbitraryDemandModule solver entry solve).length
  outerEntryBody (b+1) solve copy ::
    (inputBoundsModule (b+1) ++ (arbitraryDemandModule solver entry solve ++ [copyWords]))

/-- The whole program starts at procedure zero and has no input-dependent code. -/
def outerScalingProgram (solver : Program) (entry : ℕ) : Program :=
  Program.mk (outerEntryModule solver entry 0)

/-- The exact model answer is copied to zero, with explicit linear entry
overhead in addition to the complete arbitrary-demand machine budget. -/
noncomputable def outerEntryContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) : Contract where
  pre args mem := args=[I.encode.length] ∧ mem=initMem I.encode ∧ w=wordSize 131072 I.encode
  post _ _ ret mem' :=
    let answer := scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
      (canonicalSolver solver entry T hproc) I hv I.maxCost I.maxCapacity).value
    ret=answer.length ∧ ListAt mem' 0 answer
  cost _ _ := (arbitraryDemandContract w solver entry T hproc I hv I.maxCost I.maxCapacity).cost [] (fun _ => 0)+
    2000*(I.m+I.n+1)

/-- The entry assembly preserves determinism of the supplied solver. -/
theorem outerEntryModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈outerEntryModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [outerEntryBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact inputBoundsModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact arbitraryDemandModule_noRand solver entry _ hdet body hb
      · have he : body=copyWords := by simpa only [List.mem_singleton] using hb
        subst body
        simp only [copyWords,forRange,forUp,Stmt.NoRand,and_self]

/-- The complete program is deterministic whenever its circulation solver is. -/
theorem outerScalingProgram_deterministic (solver : Program) (entry : ℕ) (hdet : solver.IsDeterministic) :
    (outerScalingProgram solver entry).IsDeterministic := by
  exact outerEntryModule_noRand solver entry 0 hdet

end MinCostFlow.Scaling.Machine
