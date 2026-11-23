module

public import MinCostFlow.Final.ApproximationFinishWithSolver
public import MinCostFlow.Final.ScratchBottleneckSearch
public import MinCostFlow.Scaling.PolyApproxContract
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Bottleneck approximation with polynomial scratch

The search keeps a canonical threshold flow. The finishing procedure
turns that flow into the approximation candidate and preserves the
original circulation. The contract adds the two phases' costs and space.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Fresh cells reserved by the complete sorted bottleneck search. -/
def scratchBottleneckSearchSpace (c d : ℕ) (J : Circulation) : ℕ :=
  let L := Nat.clog 2 (J.m+1)
  let G := scratchBottleneckGuestBound c d J (sortCapacities (List.ofFn J.capacity)).1
  J.m+(L+1)*J.m+5+(L+1)*(12+15*J.m+2^G)

/-- Complete search followed by the cycle extraction and scatter finishing entry. -/
def scratchPolyApproxModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let finish := b+1+(scratchBottleneckSearchModule solver entry (b+1) c d).length
  polyApproxBody (b+1) finish ::
    (scratchBottleneckSearchModule solver entry (b+1) c d ++ approximationFinishModule finish)

/-- The search's actual precondition plus enough storage and arithmetic
range for extraction and objective evaluation. -/
noncomputable def scratchPolyApproxContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract where
  pre args mem := ∃ a heap,args=[a,heap] ∧
    (scratchBottleneckSearchContract w solver entry T S c d hproc J C).pre [a,heap] mem ∧
    (∀ e,J.capacity e≤U) ∧
    heap+scratchBottleneckSearchSpace c d J+10+3*J.n+33*J.m+12<2^w ∧
    (6*J.m+2)*C<2^w ∧ J.m*(C*U)<2^w ∧ 9<2^w
  post args mem ret mem' := heapArg args≤ret ∧
    ret≤heapArg args+scratchBottleneckSearchSpace c d J+10+3*J.n+33*J.m+8 ∧
    ApproximationResultAt mem' (ret-2) ret
      (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J).value ∧
    ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
  cost args mem := (scratchBottleneckSearchContract w solver entry T S c d hproc J C).cost args mem+
    9000*(J.m+1)+100

/-- The approximation entry is deterministic whenever its supplied solver is. -/
theorem scratchPolyApproxModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchPolyApproxModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [polyApproxBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hs | hf
    · exact scratchBottleneckSearchModule_noRand solver entry _ c d hdet body hs
    · exact approximationFinishModule_noRand _ body hf

/-- The complete machine approximation computes precisely `polyApproxModel`
with the actual canonical solver, charging search and linear finishing. -/
theorem scratchPolyApprox_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchPolyApproxModule solver entry b c d))
    (J : Circulation) (hnGraph : J.n ≤ 2*J.m) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) (hC : J.CostsBounded C) :
    MeetsContract w p b (scratchPolyApproxContract w solver entry T S c d hproc J C U) := by
  have ht := hasAt_tail hp
  have hkS := scratchBottleneckSearch_meetsContract (w := w) hproc hdet J hnGraph C hc hC hS (hasAt_append_left ht)
  have hkF := withSolverApproximationFinish_meetsContract (w := w)
    (fun K => compressedCanonicalSolverAt _ solver entry T S (hproc K) K)
    (fun K _ _ => compressedCanonicalSolverAt_optimal _ solver entry T S (hproc K) K)
    (hasAt_append_right ht) J C U hc
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hsearch,hcapacities,hspace,hbudget,hproduct,hw⟩ := hpre
  have hsearchCopy := hsearch
  obtain ⟨⟨a',heap',hargs,hgraph,hgraphEnd,hinput,hsmall,hmass,hguest,hwSearch⟩,hz,hs⟩ := hsearchCopy
  have heq : a=a' ∧ heap=heap' := by simpa only [List.cons.injEq,and_true] using hargs
  obtain ⟨rfl,rfl⟩ := heq
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hh : heap<2^w := by omega
  apply runs_start_le
  unfold polyApproxBody
  refine runs_seq_call_le hkS (vs := [a,heap]) (by eval_expr) hwords hsearch ?_
  intro searchEnd memS posS hpostS
  obtain ⟨⟨_,hhi,hframeS,hzS,_⟩,hlo,hstateS,hheaderS,hbestS⟩ := hpostS
  change searchEnd≤heap+scratchBottleneckSearchSpace c d J at hhi
  change heap+5≤searchEnd at hlo
  change (∀ x<heap,memS x=mem x) at hframeS
  change ZeroFrom memS searchEnd at hzS
  change BottleneckStateAt memS (searchEnd-5)
    (bottleneckSearch ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J).value at hstateS
  change (∀ i<5,memS (searchEnd-5+i)<2^w) at hheaderS
  change (∀ u flow,(bottleneckSearch ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J).value.best=some (u,flow) →
    memS (searchEnd-5+4)+J.m≤searchEnd) at hbestS
  have hsearchEndWord : searchEnd<2^w := by omega
  have hstateWord : searchEnd-5<2^w := by omega
  have hgraphS : ListAt memS a J.solverWords := hgraph.of_agree_below (h₀ := heap) hgraphEnd hframeS
  refine runs_seq_assign_le (v := searchEnd-5) (by eval_expr) ?_
  refine runs_seq_call_le hkF (vs := [a,searchEnd-5,searchEnd]) (by eval_expr) (by wram_words)
    ⟨a,searchEnd-5,searchEnd,rfl,hgraphS,by omega,by omega,hstateS,hheaderS,hbestS,
      hinput,hC,hcapacities,hzS,by omega,hbudget,hproduct,hw⟩ ?_
  intro ret memF posF hpostF
  obtain ⟨hloF,hhiF,hresultF,hzF,hframeF⟩ := hpostF
  change searchEnd≤ret at hloF
  change ret≤searchEnd+10+3*J.n+33*J.m+8 at hhiF
  change (∀ x<searchEnd,memF x=memS x) at hframeF
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+scratchBottleneckSearchSpace c d J+10+3*J.n+33*J.m+8 ∧
      ApproximationResultAt memF (ret-2) ret (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J).value ∧
      ZeroFrom memF ret ∧ ∀ x<heap,memF x=mem x
    refine ⟨by omega,by omega,hresultF,hzF,?_⟩
    intro x hx
    exact (hframeF x (by omega)).trans (hframeS x hx)
  · simp only [scratchPolyApproxContract,withSolverApproximationFinishContract,startState,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.Final
