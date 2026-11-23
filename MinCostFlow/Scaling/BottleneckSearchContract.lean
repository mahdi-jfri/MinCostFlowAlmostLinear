module

public import MinCostFlow.Scaling.CapacityCandidatesProgram
public import MinCostFlow.Scaling.ClogTwoProgram
public import MinCostFlow.Scaling.BottleneckLoopProgram

/-!
# The complete bottleneck search machine interface

Collect and sort the actual edge capacities, compute the model's binary
logarithmic round count, write the initial interval header, and execute
the exact bounded search. The final header retains the model's last
successful threshold flow for cycle extraction.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,heap]`. -/
def bottleneckSearchBody (prepare log writer loop : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 3 (.bin .add (.reg 2) (.const 1)) ;;
  .call 4 log [.reg 3] ;;
  .call 5 prepare [.reg 0,.reg 1] ;;
  .assign 6 (.bin .sub (.reg 5) (.reg 2)) ;;
  .call 7 writer [.const 0,.reg 2,.const 0,.const 0,.const 0,.reg 5] ;;
  .call 8 loop [.reg 0,.reg 6,.reg 5,.reg 4,.reg 7] ;;
  .ret (.reg 8)

/-- Preparation, ceiling logarithm, initial header, and bounded search. -/
def bottleneckSearchModule (solver : Program) (f b : ℕ) : List Stmt :=
  let log := b+1+(capacityCandidatesModule (b+1)).length
  let writer := log+1
  let loop := writer+1
  bottleneckSearchBody (b+1) log writer loop ::
    (capacityCandidatesModule (b+1) ++ clogTwoModule log ++ wordFiveModule ++ bottleneckLoopModule solver f loop)

/-- Exact search output and counted model cost. The space reserve covers
candidate sorting, an initial header, and every possible threshold guest. -/
noncomputable def bottleneckSearchContract (w : ℕ) (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (C : ℕ) : Contract :=
  let L := Nat.clog 2 (J.m+1)
  let candidates := (sortCapacities (List.ofFn J.capacity)).1
  let G := bottleneckGuestBound J candidates
  let A := 12+15*J.m+2^G
  let result := bottleneckSearch (canonicalSolver solver f T hproc) J
  let H := heapContract w
    (fun args mem => ∃ a heap,args=[a,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x<2^w) ∧
      J.m+2<2^w ∧ J.m*C<2^w ∧ 2^(G+1)+2≤2^w ∧ 8<2^w)
    (fun _ _ _ => True)
    (fun _ _ => result.calls.length*
      ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound)+200*result.work+1500)
    (fun _ _ => J.m+(L+1)*J.m+5+(L+1)*A)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      heapArg args+5≤ret ∧ BottleneckStateAt mem' (ret-5) result.value ∧
      (∀ i<5,mem' (ret-5+i)<2^w) ∧
      (∀ u flow,result.value.best=some (u,flow) → mem' (ret-5+4)+J.m≤ret) }

/-- The entire search contains no random instruction when its solver is deterministic. -/
theorem bottleneckSearchModule_noRand (solver : Program) (f b : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ bottleneckSearchModule solver f b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckSearchBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hl
    · rcases List.mem_append.mp hb with hb | hw
      · rcases List.mem_append.mp hb with hc | hg
        · exact capacityCandidatesModule_noRand _ body hc
        · have he : body=clogTwoBody (b+1+(capacityCandidatesModule (b+1)).length) := by
            simpa only [clogTwoModule,List.mem_singleton] using hg
          subst body
          exact clogTwoBody_noRand _
      · have he : body=wordFiveBody := by simpa only [wordFiveModule,List.mem_singleton] using hw
        subst body
        exact wordFiveBody_noRand
    · exact bottleneckLoopModule_noRand solver f _ hdet body hl

/-- The complete search uses at most a ceiling-logarithmic number of
solver calls and linear-logarithmic model work. -/
theorem bottleneckSearch_cost_le (w : ℕ) (solver : Program) (f : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (J : Circulation) (C : ℕ) (args : List ℕ) (mem : ℕ → ℕ) :
    (bottleneckSearchContract w solver f T hproc J C).cost args mem ≤
      Nat.clog 2 (J.m+1)*((solver.regBound+6)*T (J.n+1) J.m+
        40*bottleneckGuestBound J (sortCapacities (List.ofFn J.capacity)).1+solver.regBound)+
      24000*(Nat.clog 2 (J.m+1)+1)*(J.m+1)+1500 := by
  have hc := bottleneckSearch_calls (canonicalSolver solver f T hproc) J
  have hw := bottleneckSearch_work (canonicalSolver solver f T hproc) J
  let B := (solver.regBound+6)*T (J.n+1) J.m+
    40*bottleneckGuestBound J (sortCapacities (List.ofFn J.capacity)).1+solver.regBound
  change (bottleneckSearch (canonicalSolver solver f T hproc) J).calls.length*B+
    200*(bottleneckSearch (canonicalSolver solver f T hproc) J).work+1500 ≤ _
  have hc' := Nat.mul_le_mul_right B hc
  have hw' := Nat.mul_le_mul_left 200 hw
  have hbound := Nat.add_le_add_right (Nat.add_le_add hc' hw') 1500
  simpa only [←Nat.mul_assoc] using hbound

end MinCostFlow.Scaling.Machine
