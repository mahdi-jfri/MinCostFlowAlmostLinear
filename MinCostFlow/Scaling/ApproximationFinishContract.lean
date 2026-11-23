module

public import MinCostFlow.Scaling.ApproximationLayout
public import MinCostFlow.Scaling.BottleneckSearchContract
public import MinCostFlow.Scaling.ExtractCycleContract
public import MinCostFlow.Scaling.CycleCandidateContract
import WordRAM.Logic

/-!
# Completing an approximation from the exact search result

An unsuccessful search returns a zero candidate. A retained unit flow is
scanned for a negative cycle. If a cycle is returned, scatter the retained
threshold along it and compute the objective magnitude. Otherwise return
the zero candidate. The result uses the common two-word header.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Return a zero flow candidate using the common candidate constructor. -/
def approximationZeroCall (candidate : ℕ) (heap : Expr) : Stmt :=
  .call 9 candidate [.reg 0,.const 0,.const 0,heap] ;; .ret (.reg 9)

/-- Arguments `[graph,searchState,heap]`. -/
def approximationFinishBody (extract candidate : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .cond (.bin .eq (.reg 3) (.const 0))
    (approximationZeroCall candidate (.reg 2))
    (.assign 5 (.load (.bin .add (.reg 1) (.const 3))) ;;
     .assign 6 (.load (.bin .add (.reg 1) (.const 4))) ;;
     .call 7 extract [.reg 0,.reg 6,.reg 2] ;;
     .assign 8 (.load (.bin .add (.reg 2) (.const 7))) ;;
     .cond (.bin .eq (.reg 8) (.const 1))
       (.call 9 candidate [.reg 0,.load (.bin .add (.reg 2) (.const 8)),.reg 5,.reg 7] ;;
        .ret (.reg 9))
       (approximationZeroCall candidate (.reg 7)))

/-- Finishing entry followed by extraction and candidate construction. -/
def approximationFinishModule (b : ℕ) : List Stmt :=
  let candidate := b+1+(extractCycleModule (b+1)).length
  approximationFinishBody (b+1) candidate ::
    (extractCycleModule (b+1) ++ cycleCandidateModule candidate)

/-- The retained search header is the actual model header. All other
premises describe represented data and numerical reserves. -/
noncomputable def approximationFinishContract (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U : ℕ) : Contract where
  pre args mem := ∃ a state heap,args=[a,state,heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length≤heap ∧ state+5≤heap ∧
    BottleneckStateAt mem state (bottleneckSearch (canonicalSolver solver entry T hproc) J).value ∧
    (∀ i<5,mem (state+i)<2^w) ∧
    (∀ u flow,(bottleneckSearch (canonicalSolver solver entry T hproc) J).value.best=some (u,flow) →
      mem (state+4)+J.m≤heap) ∧
    (∀ x ∈ J.solverWords,x<2^w) ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
    ZeroFrom mem heap ∧ heap+10+3*J.n+33*J.m+12<2^w ∧
    (6*J.m+2)*C<2^w ∧ J.m*(C*U)<2^w ∧ 9<2^w
  post args mem ret mem' := heapArg args≤ret ∧
    ret≤heapArg args+10+3*J.n+33*J.m+8 ∧
    ApproximationResultAt mem' (ret-2) ret
      (polyApproxModel (canonicalSolver solver entry T hproc) J).value ∧
    ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
  cost _ _ := 9000*(J.m+1)

/-- Finishing uses only deterministic extraction and scatter procedures. -/
theorem approximationFinishModule_noRand (b : ℕ) :
    ∀ body ∈ approximationFinishModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [approximationFinishBody,approximationZeroCall,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with he | hc
    · exact extractCycleModule_noRand _ body he
    · exact cycleCandidateModule_noRand _ body hc

end MinCostFlow.Scaling.Machine
