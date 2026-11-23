module

public import MinCostFlow.Scaling.ApproximationFinishContract

/-!
# The complete bottleneck approximation entry

Run the sorted bottleneck search and pass its retained header to the
finishing entry. The output is the exact approximation model value. The
cost separates the search's solver calls from the linear extraction and
scatter work, and reserves both phases' fresh storage together.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Fresh cells reserved by the complete sorted bottleneck search. -/
def bottleneckSearchSpace (J : Circulation) : ℕ :=
  let L := Nat.clog 2 (J.m+1)
  let G := bottleneckGuestBound J (sortCapacities (List.ofFn J.capacity)).1
  J.m+(L+1)*J.m+5+(L+1)*(12+15*J.m+2^G)

/-- Arguments `[graph,heap]`. -/
def polyApproxBody (search finish : ℕ) : Stmt :=
  .call 2 search [.reg 0,.reg 1] ;;
  .assign 3 (.bin .sub (.reg 2) (.const 5)) ;;
  .call 4 finish [.reg 0,.reg 3,.reg 2] ;;
  .ret (.reg 4)

/-- Complete search followed by the cycle extraction and scatter finishing entry. -/
def polyApproxModule (solver : Program) (entry b : ℕ) : List Stmt :=
  let finish := b+1+(bottleneckSearchModule solver entry (b+1)).length
  polyApproxBody (b+1) finish ::
    (bottleneckSearchModule solver entry (b+1) ++ approximationFinishModule finish)

/-- The search's actual precondition plus enough storage and arithmetic
range for extraction and objective evaluation. -/
noncomputable def polyApproxContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract where
  pre args mem := ∃ a heap,args=[a,heap] ∧
    (bottleneckSearchContract w solver entry T hproc J C).pre [a,heap] mem ∧
    (∀ e,J.capacity e≤U) ∧
    heap+bottleneckSearchSpace J+10+3*J.n+33*J.m+12<2^w ∧
    (6*J.m+2)*C<2^w ∧ J.m*(C*U)<2^w ∧ 9<2^w
  post args mem ret mem' := heapArg args≤ret ∧
    ret≤heapArg args+bottleneckSearchSpace J+10+3*J.n+33*J.m+8 ∧
    ApproximationResultAt mem' (ret-2) ret
      (polyApproxModel (canonicalSolver solver entry T hproc) J).value ∧
    ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
  cost args mem := (bottleneckSearchContract w solver entry T hproc J C).cost args mem+
    9000*(J.m+1)+100

/-- The approximation entry is deterministic whenever its supplied solver is. -/
theorem polyApproxModule_noRand (solver : Program) (entry b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ polyApproxModule solver entry b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [polyApproxBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hs | hf
    · exact bottleneckSearchModule_noRand solver entry _ hdet body hs
    · exact approximationFinishModule_noRand _ body hf

end MinCostFlow.Scaling.Machine
