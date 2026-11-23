module

public import MinCostFlow.Final.ScratchBottleneckStep
public import MinCostFlow.Scaling.BottleneckLoopContract
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Running the bottleneck search with polynomial scratch

The recursive loop preserves the search state and charges each threshold
test once. Its reservation bounds all steps by the largest guest region
for any threshold in the candidate array.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Recursive loop entry followed by the complete step module. -/
def scratchBottleneckLoopModule (solver : Program) (f b c d : ℕ) : List Stmt :=
  bottleneckLoopBody b (b+1) :: scratchBottleneckStepModule solver f (b+1) c d

/-- The exact finite model loop. One extra step's space is reserved to
make the same source-layout premises available even at zero rounds. -/
noncomputable def scratchBottleneckLoopContract (w : ℕ) (solver : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (candidates : List ℕ) (s : BottleneckState J) (C rounds : ℕ) : Contract :=
  let G := scratchBottleneckGuestBound c d J candidates
  let A := 12+15*J.m+2^G
  let result := CallResult.forRounds (BottleneckState.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) candidates) rounds s
  let H := heapContract w
    (fun args mem => ∃ a vec state heap,args=[a,vec,state,rounds,heap] ∧
      (scratchBottleneckStepContract w solver f T S c d hproc J candidates s C).pre [a,vec,state,heap] mem ∧
      state+5=heap ∧ rounds<2^w)
    (fun _ _ _ => True)
    (fun _ _ => result.calls.length*
      ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound)+200*result.work+20)
    (fun _ _ => (rounds+1)*A)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      ret ≤ heapArg args+rounds*A ∧
      BottleneckStateAt mem' (ret-5) result.value ∧
      (∀ i<5,mem' (ret-5+i)<2^w) ∧
      (∀ u flow,result.value.best=some (u,flow) → mem' (ret-5+4)+J.m ≤ ret) }

/-- Every bounded loop procedure is deterministic when its solver is. -/
theorem scratchBottleneckLoopModule_noRand (solver : Program) (f b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchBottleneckLoopModule solver f b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckLoopBody,Stmt.NoRand,and_self]
  · exact scratchBottleneckStepModule_noRand solver f _ c d hdet body hb

private theorem loop_cost_padding (a b B W V stepCost : ℕ)
    (hstep : stepCost≤b*B+200*V) :
    0+(1+1+1)+1+(1+(1+(1+(1+1+1+(1+0)))))+(a*B+200*W+20)+2+
      (1+1+1)+2+(1+(1+(1+(1+0))))+stepCost+2+(1+1) ≤
      (a+b)*B+200*(W+(V+1))+20 := by
  rw [Nat.add_mul]
  omega

/-- Every finite machine loop computes the exact model `forRounds`, with
cost proportional to its recorded solver calls and non-solver work. -/
theorem scratchBottleneckLoop_meetsContract {w b : ℕ} {P solver : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hdet : solver.IsDeterministic) (J : Circulation) (hnGraph : J.n ≤ 2*J.m) (candidates : List ℕ)
    (s : BottleneckState J) (C rounds : ℕ) (hc : J.CostsBounded (J.m^10)) (hC : J.CostsBounded C)
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hp : P.HasAt b (scratchBottleneckLoopModule solver f b c d)) :
    MeetsContract w P b (scratchBottleneckLoopContract w solver f T S c d hproc J candidates s C rounds) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)
  let G := scratchBottleneckGuestBound c d J candidates
  let A := 12+15*J.m+2^G
  have hG : 0<2^G := Nat.two_pow_pos G
  have hA : 5≤A := by dsimp only [A]; omega
  induction rounds generalizing s with
  | zero =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,vec,state,heap,rfl,hstepPre,hstateEnd,_⟩,hz,hs⟩ := hpre
    obtain ⟨⟨a',vec',state',heap',hargs,hgraph,hvec,hstate,hgraphEnd,hvecEnd,hheaderEnd,
      hinput,hvalues,hheader,hbest,hlen,hlower,hupper,hsmall,hbudget,hguest,hw⟩,_,_⟩ := hstepPre
    have heq : a=a' ∧ vec=vec' ∧ state=state' ∧ heap=heap' := by
      simpa only [List.cons.injEq,and_true] using hargs
    obtain ⟨ha,hv,ht,hh⟩ := heq
    subst a'; subst vec'; subst state'; subst heap'
    change ZeroFrom mem heap at hz
    change heap+(0+1)*A<2^w at hs
    have hhword : heap<2^w := by omega
    have hsame : heap-5=state := by omega
    apply runs_start_le
    unfold bottleneckLoopBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap≤heap ∧ heap≤heap+(0+1)*A ∧ (∀ x<heap,mem x=mem x) ∧ ZeroFrom mem heap ∧ True) ∧
          heap≤heap+0*A ∧ BottleneckStateAt mem (heap-5) s ∧
          (∀ i<5,mem (heap-5+i)<2^w) ∧ (∀ u flow,s.best=some (u,flow) → mem (heap-5+4)+J.m≤heap)
        rw [hsame]
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,True.intro⟩,by omega,hstate,hheader,hbest⟩
      · simp only [scratchBottleneckLoopContract,heapContract,CallResult.forRounds,CallResult.pure,
          List.length_nil,Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega
  | succ rounds ih =>
    have hkR := ih s
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,vec,state,heap,rfl,hstepPre,hstateEnd,hrounds⟩,hz,hs⟩ := hpre
    have hstepPreCopy := hstepPre
    obtain ⟨⟨a',vec',state',heap',hargs,hgraph,hvec,hstate,hgraphEnd,hvecEnd,hheaderEnd,
      hinput,hvalues,hheader,hbest,hlen,hlower,hupper,hsmall,hbudget,hguest,hw⟩,_,_⟩ := hstepPreCopy
    have heq : a=a' ∧ vec=vec' ∧ state=state' ∧ heap=heap' := by
      simpa only [List.cons.injEq,and_true] using hargs
    obtain ⟨ha,hv,ht,hh⟩ := heq
    subst a'; subst vec'; subst state'; subst heap'
    change ZeroFrom mem heap at hz
    change heap+(rounds+1+1)*A<2^w at hs
    simp only [Nat.add_mul,Nat.one_mul] at hs
    have hhword : heap<2^w := by omega
    have haWord : a<2^w := by omega
    have hvWord : vec<2^w := by omega
    have htWord : state<2^w := by omega
    have hrWord : rounds<2^w := by omega
    let r := CallResult.forRounds (BottleneckState.step solve candidates) rounds s
    have hint : r.value.lower≤r.value.upper ∧ r.value.upper≤J.m := by
      exact CallResult.forRounds_invariant (BottleneckState.step solve candidates)
        (fun s => s.lower≤s.upper ∧ s.upper≤J.m)
        (fun s hs => bottleneckStep_interval solve candidates s J.m hs.1 hs.2) rounds s ⟨hlower,hupper⟩
    have hkS := scratchBottleneckStep_meetsContract (w := w) hproc hdet J hnGraph candidates r.value C hc hC hS (hasAt_tail hp)
    apply runs_start_le
    unfold bottleneckLoopBody
    wram_step
    refine runs_seq_call_le hkR (vs := [a,vec,state,rounds,heap]) ?_ (by wram_words) ?_ ?_
    · have heq : rounds+1-1=rounds := rfl
      rw [←heq]
      clear! solver T G solve A r
      eval_expr
    · refine ⟨⟨a,vec,state,heap,rfl,hstepPre,hstateEnd,hrWord⟩,hz,?_⟩
      change heap+(rounds+1)*A<2^w
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · intro midHeap memR posR hpostR
      obtain ⟨⟨hlo,_,hframeR,hzR,_⟩,hhi,hstateR,hheaderR,hbestR⟩ := hpostR
      change heap≤midHeap at hlo
      change midHeap≤heap+rounds*A at hhi
      change (∀ x<heap,memR x=mem x) at hframeR
      change ZeroFrom memR midHeap at hzR
      change BottleneckStateAt memR (midHeap-5) r.value at hstateR
      change (∀ i<5,memR (midHeap-5+i)<2^w) at hheaderR
      change (∀ u flow,r.value.best=some (u,flow) → memR (midHeap-5+4)+J.m≤midHeap) at hbestR
      have hmidWord : midHeap<2^w := by omega
      have hstateWord : midHeap-5<2^w := by omega
      have hnewEnd : midHeap-5+5=midHeap := by omega
      have hgraphR := hgraph.of_agree_below hgraphEnd hframeR
      have hvecR := hvec.of_agree_below hvecEnd hframeR
      refine runs_seq_assign_le (v := midHeap-5) (by clear! solver T G solve A r; eval_expr) ?_
      refine runs_seq_call_le hkS (vs := [a,vec,midHeap-5,midHeap])
        (by clear! solver T G solve A r; eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨a,vec,midHeap-5,midHeap,rfl,hgraphR,hvecR,hstateR,
          hgraphEnd.trans hlo,hvecEnd.trans hlo,by omega,hinput,hvalues,hheaderR,hbestR,
          hlen,hint.1,hint.2,hsmall,hbudget,hguest,hw⟩,hzR,?_⟩
        change midHeap+(if r.value.lower<r.value.upper then A else 5)<2^w
        split <;> omega
      · intro ret memS posS hpostS
        obtain ⟨⟨hloS,hhiS,hframeS,hzS,_⟩,hnewLower,hstateS,hheaderS,hbestS⟩ := hpostS
        change midHeap≤ret at hloS
        change ret≤midHeap+(if r.value.lower<r.value.upper then A else 5) at hhiS
        have hallocS : ret≤midHeap+A := by split at hhiS <;> omega
        change (∀ x<midHeap,memS x=memR x) at hframeS
        change ZeroFrom memS ret at hzS
        change BottleneckStateAt memS (ret-5) (BottleneckState.step solve candidates r.value).value at hstateS
        change (∀ i<5,memS (ret-5+i)<2^w) at hheaderS
        change (∀ u flow,(BottleneckState.step solve candidates r.value).value.best=some (u,flow) →
          memS (ret-5+4)+J.m≤ret) at hbestS
        have hr : ret<2^w := by omega
        refine runs_ret_le (v := ret) (by clear! solver T G solve A r; eval_expr) ?_ ?_
        · change (heap≤ret ∧ ret≤heap+(rounds+1+1)*A ∧ (∀ x<heap,memS x=mem x) ∧ ZeroFrom memS ret ∧ True) ∧
            ret≤heap+(rounds+1)*A ∧
            BottleneckStateAt memS (ret-5) (CallResult.forRounds (BottleneckState.step solve candidates) (rounds+1) s).value ∧
            (∀ i<5,memS (ret-5+i)<2^w) ∧ _
          simp only [Nat.add_mul,Nat.one_mul]
          refine ⟨⟨by omega,by omega,?_,hzS,True.intro⟩,by omega,hstateS,hheaderS,hbestS⟩
          intro x hx
          exact (hframeS x (by omega)).trans (hframeR x hx)
        · have hcost := scratchBottleneckStep_cost_model_le w solver f T S c d hproc J candidates r.value C [a,vec,midHeap-5,midHeap] memR
          simp only [scratchBottleneckLoopContract,heapContract,CallResult.forRounds,CallResult.bind,CallResult.charge,
            List.length_append,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
          exact loop_cost_padding r.calls.length _ _ r.work _ _ hcost

end MinCostFlow.Final
