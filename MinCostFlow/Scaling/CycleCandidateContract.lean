module

public import MinCostFlow.Scaling.IndexScatterProgram
public import MinCostFlow.Scaling.IntegerObjectiveProgram
public import MinCostFlow.Scaling.WordPairProgram
import WordRAM.Logic

/-!
# Constructing a flow and magnitude from a returned cycle

Scatter the bottleneck amount along the immutable edge list into a fresh
zero flow array. Compute its full signed integer objective. Its negation's
nonnegative part is the approximation magnitude. Return a two-word header
containing the flow pointer and that magnitude.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Store a prepared magnitude together with the allocated flow pointer. -/
def cycleCandidateWrite (pair : ℕ) (magnitude : Expr) : Stmt :=
  .call 10 pair [.reg 3,magnitude,.reg 7] ;; .ret (.reg 10)

/-- Arguments `[graph,list,value,heap]`. -/
def cycleCandidateBody (scatter objective pair : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.reg 3) (.reg 4)) ;;
  .call 6 scatter [.reg 1,.reg 2,.reg 3] ;;
  .call 7 objective [.reg 0,.reg 3,.reg 5] ;;
  .assign 8 (.load (.bin .sub (.reg 7) (.const 2))) ;;
  .cond (.bin .eq (.reg 8) (.const 1))
    (cycleCandidateWrite pair (.load (.bin .sub (.reg 7) (.const 1))))
    (cycleCandidateWrite pair (.const 0))

/-- Consecutive entries for the candidate, list scatter, objective, and header. -/
def cycleCandidateModule (b : ℕ) : List Stmt :=
  let objective := b+2
  let pair := objective+(integerObjectiveModule objective).length
  cycleCandidateBody (b+1) objective pair ::
    (indexScatterModule (b+1) ++ integerObjectiveModule objective ++ wordPairModule)

/-- Exact unsigned flow and objective magnitude, retaining the source
prefix and the fresh zero tail. -/
def cycleCandidateContract (w lo : ℕ) (J : Circulation) (es : List (Fin J.m)) (u C : ℕ) : Contract where
  pre args mem := ∃ a ptr heap,args=[a,ptr,u,heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length≤heap ∧ IndexListAt mem lo heap ptr es ∧
    (∀ x ∈ J.solverWords,x<2^w) ∧ J.CostsBounded C ∧ J.m*(C*u)<2^w ∧
    ZeroFrom mem heap ∧ heap+5*J.m+4<2^w ∧ 8<2^w
  post args mem ret mem' :=
    let f := Scatter.write (fun _ : Fin J.m => (0 : ℕ)) (es.map (fun e => (e,u)))
    ret=heapArg args+5*J.m+4 ∧ ListAt mem' (heapArg args) (List.ofFn f) ∧
    ListAt mem' (ret-2) [heapArg args,(-(J.integerObjective (fun e => (f e : ℤ)))).toNat] ∧
    ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
  cost _ _ := 500*J.m+60*es.length+500

/-- All candidate construction instructions and callees are deterministic. -/
theorem cycleCandidateModule_noRand (b : ℕ) : ∀ body ∈ cycleCandidateModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cycleCandidateBody,cycleCandidateWrite,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hp
    · rcases List.mem_append.mp hb with hs | ho
      · exact indexScatterModule_noRand _ body hs
      · exact integerObjectiveModule_noRand _ body ho
    · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hp
      subst body
      exact wordPairBody_noRand

end MinCostFlow.Scaling.Machine
